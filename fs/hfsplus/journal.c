/*
 * linux/fs/hfsplus/journal.c
 *
 * Copyright (c) 2013, Nathaniel Yazdani <n1ght.4nd.d4y@gmail.com>
 *
 * HFS+ journaling infrastructure
 *
 * HFS+ records metadata I/O in an on-disk journal, which this code provides an
 * interface to. A journaled transaction begins with a call to
 * hfsplus_start_transact() (nestiing okay) and ends with
 * hfsplus_transact_stop(), which writes the transaction to the journal.
 * Between these two calls, hfsplus_transactact_page() is used to collect modified
 * pages into a single transaction. A transaction is only committed (indicated
 * as valid in the journal header) when the bi_end_io handler of a completed
 * transaction's bio is called. Currently, transactions are not tracked
 * end-to-end, so to clear the journal the entire filesystem must be synchronized.
 * The journal buffer is written until fully filled, then we wait until all
 * transactions are fully flushed.
 *
 * TODO: private slabs are a good idea for this code
 */

#include <linux/types.h>
#include <linux/slab.h>
#include <linux/string.h>
#include <linux/fs.h>
#include <linux/blkdev.h>
#include <linux/bio.h>
#include <linux/mutex.h>
#include <asm/page.h>
#include <asm/unaligned.h>

#include "hfsplus_raw.h"
#include "hfsplus_fs.h"


#define offset2sector(off) ((off) >> HFSPLUS_SECTOR_SHIFT)
#define sector2offset(sec) ((sec) << HFSPLUS_SECTOR_SHIFT)


/* in-progress journal transaction */
struct hfsplus_transact {
	struct super_block *sb;
	unsigned char depth;
	unsigned short count;
	struct page *pages[1];
}; /* current->journal_info */

/* in-progress journal commit */
struct hfsplus_commit {
	struct hfsplus_blhdr *blist; /* so we can release the memory */
	sector_t sector;
	sector_t length;
};

static struct hfsplus_blhdr *hfsplus_process_transact(void);
static int hfsplus_replay_transact(struct super_block *sb,
				 const struct hfsplus_blhdr *blist,
				 const void *blocks);
static int hfsplus_read_transact(struct super_block *sb,
			       struct hfsplus_blhdr **blist,
			       void **blocks);
static int hfsplus_write_transact(void);
static void hfsplus_submit_transact(struct bio *bio, bool lock);
static void hfsplus_cancel_transact(void);
static void hfsplus_commit_transact(struct bio *, int); /* bi_end_io */
static void hfsplus_finish_transact(struct buffer_head *, int); /* bh_end_io */

__be32 hfsplus_checksum(const void *ptr, size_t len)
{
	int i;
	uint32_t res = 0;
	for (i = 0; i < len; ++i)
		res = (res << 8) ^ (res + ((char *)ptr)[i]);
	return cpu_to_be32(res);
}

/*
 * Synchronize journal header. Called under journal mutex.
 */
static int hfsplus_synch_journal(struct super_block *sb, bool wait)
{
	struct hfsplus_sb_info *sbi = HFSPLUS_SB(sb);
	struct bio *bio;
	size_t size = be32_to_cpu(sbi->journal_hdr->jhdr_sz);

	bio = bio_alloc(GFP_NOFS, 1);
	bio->bi_iter.bi_sector = sbi->journal;

	if (bio_add_page(bio, virt_to_page(sbi->journal_hdr), size,
			 (off_t)sbi->journal_hdr % PAGE_SIZE) != size) {
		bio_put(bio);
		return -EIO;
	}

	sbi->journal_hdr->oldest = cpu_to_be64(sector2offset(sbi->journal_end));
	sbi->journal_hdr->newest = cpu_to_be64(sector2offset(sbi->journal_cur));
	sbi->journal_hdr->checksum = 0;
	sbi->journal_hdr->checksum = hfsplus_checksum(sbi->journal_hdr,
						sizeof(struct hfsplus_jhdr));
	if (wait)
		return submit_bio_wait(WRITE_SYNC, bio);
	else
		submit_bio(WRITE, bio);
	return 0;
}

/*
 * Replay any transactions remaining in the journal, called only when bringing
 * up the filesystem.
 */
int hfsplus_replay_journal(struct super_block *sb)
{
	struct hfsplus_sb_info *sbi = HFSPLUS_SB(sb);
	struct hfsplus_blhdr *blist = NULL;
	void *blocks = NULL;
	int ret;

	if (sbi->journal_hdr->oldest == sbi->journal_hdr->newest)
		goto done;

	if (be64_to_cpu(sbi->journal_hdr->oldest) % sb->s_blocksize) {
		pr_crit("ill-aligned journal on %s\n", sb->s_id);
		return -EINVAL;
	}

	pr_info("replaying journal on %s\n", sb->s_id);
	while (sbi->journal_hdr->oldest != sbi->journal_hdr->newest) {

		ret = hfsplus_read_transact(sb, &blist, &blocks);
		if (!ret)
			return -ENOMEM;

		ret = hfsplus_replay_transact(sb, blist, blocks);
		kfree(blist);
		kfree(blocks);

		/* try to update journal header (not critical) */
		hfsplus_synch_journal(sb, false);
	}

done:
	return hfsplus_synch_journal(sb, true);
}

static int hfsplus_replay_transact(struct super_block *sb,
				 const struct hfsplus_blhdr *blist,
				 const void *blocks)
{
	struct bio *bio;
	const char *ptr = blocks;
	uint64_t blk;
	uint32_t len;
	uint16_t idx;
	int error;

	/* iterate over every block entry of the transaction except the first */
	for (idx = 1; idx < be16_to_cpu(blist->count); ++idx) {

		blk = be64_to_cpu(blist->info[idx].block);
		len = be32_to_cpu(blist->info[idx].bytes);
		if (!len || blk == HFSPLUS_BLENT_SKIP)
			continue;

		bio = bio_alloc(GFP_NOFS, 1);
		bio->bi_bdev = sb->s_bdev;
		bio->bi_iter.bi_sector = blk << HFSPLUS_SB(sb)->blockoffset;

		error = -EIO;
		if (len != bio_add_page(bio, virt_to_page(ptr), len,
					(loff_t)ptr % PAGE_SIZE))
			goto err;

		error = submit_bio_wait(WRITE_SYNC, bio);
		if (error)
			goto err;

		bio_put(bio);
		ptr += len;
	}
	return 0;

err:
	bio_put(bio);
	return error;
}

/*
 * Synchronously read a record, starting at sbi->journal_end, wrapping
 * around if necessary. All memory is kmalloc()ed.
 */
static int hfsplus_read_transact(struct super_block *sb,
			       struct hfsplus_blhdr **blist,
			       void **blocks)
{
	struct hfsplus_sb_info *sbi = HFSPLUS_SB(sb);
	struct bio *bio = NULL;
	void *ptr;
	size_t cur, len;
	int error = 0;

	if (!blist || !blocks)
		return -EINVAL;

	*blist = NULL;
	*blocks = NULL;

	/* first read in block list */
	len = sbi->blist_len;

read:
	ptr = kmalloc(len, GFP_NOFS);
	error = -ENOMEM;
	if (!ptr)
		goto err;
	cur = min_t(size_t, len, sector2offset(sbi->journal_buf +
					sbi->journal_len - sbi->journal_end));

	do {
		len -= cur;
		bio = bio_alloc(GFP_NOFS, 1);
		bio->bi_bdev = sb->s_bdev;
		bio->bi_iter.bi_sector = sbi->journal_end;
		bio->bi_iter.bi_size = (unsigned int)cur;

		error = -EIO;
		if (bio_add_page(bio, virt_to_page(ptr), cur,
						(loff_t)ptr % PAGE_SIZE) != cur)
			goto err;
		if (submit_bio_wait(READ_SYNC, bio))
			goto err;

		bio_put(bio);


		cur = len;
	} while (cur);

	/* determine whether we need to wrap around */
	if (*blist == NULL) {
		*blist = ptr;
		/* advance sbi->journal_end, potentially wrapping around */
		len = be32_to_cpu((*blist)->length);
		sbi->journal_end += len;
		sbi->journal_end %= sbi->journal_len;
		len -= sbi->blist_len; /* we already read in the block list */
		goto read;
	}
	*blocks = ptr;
	return 0;

err:
	if (*blist)
		kfree(*blist);
	if (*blocks)
		kfree(*blocks);
	if (bio)
		bio_put(bio);
	return error;
}

/*
 * Begin recording a transaction.
 */
int hfsplus_start_transact(struct super_block *sb)
{
	struct hfsplus_transact *trans = current->journal_info;

	if (!HFSPLUS_SB(sb)->journaling)
		return -ENOSYS; /* journaling disabled */

	if (trans) {
		trans->depth++;
		return 0;
	}

	current->journal_info = trans = kmalloc(sizeof *trans, GFP_NOFS);
	if (unlikely(!trans))
		return -ENOMEM;
	trans->sb = sb;
	trans->depth = 0;
	trans->count = 0;
	return 0;
}

/*
 * Queue a dirtied page (locking it as well) in the ongoing transaction, to be
 * synched after it's been recorded in the journal, _if_ journaling is active.
 */
int hfsplus_transact_page(struct page *page)
{
	struct hfsplus_transact *trans = current->journal_info, *retrans;
	size_t size;

	set_page_dirty(page);

	if (!trans)
		return 0;

	if (trans->sb != page->mapping->host->i_sb)
		return -EINVAL;

	size = ksize(trans);
	if (size < sizeof(*trans) + sizeof(page) * (trans->count)) {
		retrans = kmalloc(size + sizeof(page), GFP_NOFS);
		if (!retrans)
			return -ENOMEM;
		memcpy(trans, retrans, size);
		current->journal_info = retrans;
		kfree(trans);
	}

	lock_page(page); /* can't let any other context touch this page */
	trans->pages[trans->count++] = page;
	return 0;
}

/*
 * Either cancel or commit the record depending on the success of the operation.
 */
int hfsplus_stop_transact(int error)
{
	if (!current->journal_info)
		return error ? -EINVAL : error;

	if (!error)
		error = hfsplus_write_transact();
	else
		hfsplus_cancel_transact();

	return error;
}

/*
 * Cancel the currently active transaction.
 */
static void hfsplus_cancel_transact(void)
{
	struct hfsplus_transact *trans = current->journal_info;

	if (trans->depth) {
		/* give callers a chance to try to recover */
		trans->depth--;
		return;
	}

	current->journal_info = NULL;
	while (trans->count--)
		unlock_page(trans->pages[trans->count]);
	kfree(trans);
	return;
}

/*
 * Write the completed transaction to the journal on disk, chaining writeback
 * of recorded pages on completion. On error, pages are flagges as dirty and
 * unlocked, meaning that they will be journaled but possibly not in order.
 */
static int hfsplus_write_transact(void)
{
	struct hfsplus_transact *trans = current->journal_info;
	struct bio *bio = NULL;
	int i, error = 0;

	if (trans->depth) {
		trans->depth--;
		return 0;
	}

	if (!trans->count)
		return 0;

	/* initialize bio */
	bio = bio_alloc(GFP_NOFS, 1 + trans->count);
	bio->bi_bdev = trans->sb->s_bdev;
	bio->bi_end_io = hfsplus_commit_transact;
	/* hfsplus_submit_transact() wants this */
	bio->bi_private = hfsplus_process_transact();

	error = -ENOMEM;
	if (!bio->bi_private)
		goto err;

	error = -EIO;
	i = HFSPLUS_SB(trans->sb)->blist_len; /* borrow i for a moment */
	if (bio_add_page(bio, virt_to_page(bio->bi_private), i,
				(off_t)bio->bi_private % PAGE_SIZE) != i)
		goto err;
	for (i = 0; i < trans->count; ++i)
		if (bio_add_page(bio, trans->pages[i], PAGE_SIZE, 0) != PAGE_SIZE)
			goto err;

	hfsplus_submit_transact(bio, true);
	error = 0;
	goto out;
	
err:
	while (trans->count--)
		set_bit(PG_error, &trans->pages[trans->count]->flags);

	kfree(bio->bi_private);
out:
	current->journal_info = NULL;
	kfree(trans);
	return error;
}

/*
 * Submit a transaction's bio to the journal, or queue it if too big
 */
static void hfsplus_submit_transact(struct bio *bio, bool lock)
{
	struct hfsplus_sb_info *sbi = HFSPLUS_SB(bio->bi_bdev->bd_super);
	struct bio *split, **queue = &sbi->journal_bio;
	struct hfsplus_commit *comm;

	comm = kmalloc(sizeof(*comm), GFP_NOFS);

	/* grab the mutex to get some space in the journal buffer */
	if (lock)
		mutex_lock(&sbi->journal_mtx);
	if (!comm || (sbi->journal_len + sbi->journal_end - sbi->journal_ptr) %
					sbi->journal_len < bio_sectors(bio)) {
		/* queue bio instead of returning ENOMEM or ENOSPC */
		while (queue && *queue != bio)
			queue = &(*queue)->bi_next;
		*queue = bio;
		goto out;
	}

	/* reserve space then advance journal pointer */
	bio->bi_iter.bi_sector = sbi->journal_ptr;
	sbi->journal_ptr += bio_sectors(bio);
	sbi->journal_ptr %= sbi->journal_ptr;

	/* store info needed by hfsplus_commit_transact() */
	comm->sector = bio->bi_iter.bi_sector;
	comm->length = bio_sectors(bio);
	comm->blist = bio->bi_private;
	bio->bi_private = comm;

	/* do we need to wrap-around? */
	if (sbi->journal_len - sbi->journal_ptr > bio_sectors(bio)) {
		split = bio_clone(bio, GFP_NOFS);
		split->bi_private = NULL;
		split->bi_end_io = NULL; /* no double accounting */
		split->bi_iter.bi_sector = sbi->journal_buf;
		bio->bi_iter.bi_size = sector2offset(sbi->journal_len -
						     sbi->journal_ptr);
		bio_advance_iter(split, &split->bi_iter, bio->bi_iter.bi_size);
		submit_bio(WRITE, split);
		bio_put(split);
	}

	/* dequeue if bio was taken off the queue */
	if (sbi->journal_bio == bio)
		sbi->journal_bio = bio->bi_next;

	comm->sector = bio->bi_iter.bi_sector;
	submit_bio(WRITE, bio);
	bio_put(bio);

out:
	if (lock)
		mutex_unlock(&sbi->journal_mtx);
	return;
}

/* create a block list for the current transaction */
static struct hfsplus_blhdr *hfsplus_process_transact(void)
{
	struct hfsplus_transact *trans = current->journal_info;
	struct hfsplus_sb_info *sbi = HFSPLUS_SB(trans->sb);
	struct hfsplus_blhdr *blist;
	uint64_t block;
	uint32_t bytes;
	unsigned dst, src = 0;

	/* if a transactions is this huge, something went very wrong */
	BUG_ON((trans->count << PAGE_SHIFT) + sbi->blist_len >
					sector2offset(sbi->journal_len));

	blist = kzalloc(sbi->blist_len, GFP_NOFS);
	if (!blist)
		return NULL;

	/* skip the first entry (used to chain block lists together) */
	for (dst = 1; src < trans->count && dst < sbi->blist_num; ++src) {
		blist->info[dst].block =
			cpu_to_be64(hfsplus_bmap(trans->pages[src]->mapping,
						trans->pages[src]->index >>
						HFSPLUS_SECTOR_SHIFT) >>
						sbi->blockoffset);
		blist->info[dst].bytes = cpu_to_be32(PAGE_SIZE);

		/* try to coalesce with the previous entry */
		bytes = be32_to_cpu(blist->info[dst - 1].bytes);
		block = be64_to_cpu(blist->info[dst - 1].block) +
					(bytes >> trans->sb->s_blocksize_bits);
		if (block == be64_to_cpu(blist->info[dst].block))
			blist->info[dst - 1].bytes = cpu_to_be32(bytes + PAGE_SIZE);
		else
			dst++;
	}

	/* larger transactions chain togather multiple block lists */
	if (src != trans->count)
		/*blist->info[0].next = cpu_to_be32(src)*/;

	blist->length = cpu_to_be32(sbi->blist_len + (dst - 1) * PAGE_SIZE);
	blist->count = cpu_to_be16(dst);
	blist->checksum = hfsplus_checksum(blist, sizeof(struct hfsplus_blhdr)
						+ sizeof(struct hfsplus_blent));

	return blist;
}

/*
 * Advance sbi->journal_cur and synchronize affected buffers.
 */
static void hfsplus_commit_transact(struct bio *bio, int err) /* bi_end_io */
{
	struct hfsplus_sb_info *sbi = HFSPLUS_SB(bio->bi_bdev->bd_super);
	struct writeback_control wbc = { };
	struct hfsplus_commit *comm = bio->bi_private;
	struct bvec_iter bi = { .bi_sector = comm->sector,
				.bi_size = sector2offset(comm->length) };
	struct bio_vec bv;

	if (err) {
		/* can't do much more than acknowledge the error */
		__bio_for_each_segment(bv, bio, bi, bi)
			set_bit(PG_error, &bv.bv_page->flags);	
		pr_crit("journaling I/O error %d on %s\n", err,
						bio->bi_bdev->bd_super->s_id);
	}

	kfree(comm->blist); /* free block list */
	kfree(comm); /* don't need this anymore */
	bio_advance_iter(bio, &bi, sbi->blist_len); /* we want the payload */
	wbc.nr_to_write = bi.bi_size >> PAGE_CACHE_SHIFT;
	wbc.for_sync = 1; /* should be done sooner rather than later */

	/*
	 * The journal is written sequentially & under sbi->journal_mtx, so
	 * any prior I/O would have already been submitted before this bio.
	 * Thus, it's safe to advance the current journal offset and to update
	 * the journal header.
	 */
	mutex_lock(&sbi->journal_mtx);
	sbi->journal_cur += offset2sector(bi.bi_size + sbi->blist_len);
	sbi->journal_hdr->newest = cpu_to_be64(sector2offset(sbi->journal_cur));
	sbi->journal_hdr->checksum = 0;
	sbi->journal_hdr->checksum = hfsplus_checksum(sbi->journal_hdr,
						sizeof(struct hfsplus_jhdr));
	hfsplus_submit_bio(bio->bi_bdev->bd_super, sbi->journal,
						sbi->journal_hdr, NULL,	WRITE);
	sbi->journal_fin += offset2sector(sbi->blist_len);
	mutex_unlock(&sbi->journal_mtx);

	/* now try to synchronize pages */
	__bio_for_each_segment(bv, bio, bi, bi)
		block_write_full_page_endio(bv.bv_page, hfsplus_get_block,
						&wbc, hfsplus_finish_transact);

	return;
}

/* 
 * Advance sbi->journal_fin & check if the journal can be cleared
 */
static void hfsplus_finish_transact(struct buffer_head *bh, int uptodate)
{
	struct hfsplus_sb_info *sbi = HFSPLUS_SB(bh->b_bdev->bd_super);
	struct writeback_control wbc = { .nr_to_write = 1, .for_sync = 1 };
	struct bio *bio;

	mutex_lock(&sbi->journal_mtx);

	/* advance finished journal offset if successful, otherwise try again */
	if (uptodate)
		sbi->journal_fin += bh->b_size >> HFSPLUS_SECTOR_SHIFT;
	else
		block_write_full_page_endio(bh->b_page, hfsplus_get_block,
					    &wbc, hfsplus_finish_transact);

	/* clean up the journal if this is the last transacted page */
	if (sbi->journal_cur == sbi->journal_fin) {
		sbi->journal_end += sbi->journal_fin;
		sbi->journal_cur = 0;
		sbi->journal_fin = 0;
		/* update journal header */
		hfsplus_synch_journal(bh->b_bdev->bd_super, false);
		/* now submit queued transactions */
		for (bio = sbi->journal_bio; bio; bio = bio->bi_next)
			hfsplus_submit_transact(bio, false);
	}

	mutex_unlock(&sbi->journal_mtx);

	end_buffer_async_write(bh, uptodate);

	return;
}
