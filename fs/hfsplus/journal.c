/*
 *  linux/fs/hfsplus/journal.c
 *
 * Copyright (c) 2014, Nathaniel Yazdani <n1ght.4nd.d4y@gmail.com>
 *
 * HFS+ journaling infrastructure
 *
 * HFS+ records metadata I/O in an on-disk journal, which this code provides an
 * interface to. A journalled transaction begins with a call to
 * hfsplus_journal_start() (nesting okay) and concludes with hfsplus_journal_stop(),
 * which writes the transaction to the journal. Between these two calls, calls
 * to hfsplus_jouranl_page() queues dirtied buffers into a single transaction,
 * referred to as a block list. A transaction is only marked valid in the
 * journal header after it is completely and successfully written to the
 * journal buffer on disk (tracked with an endio routine).
 *
 * A transaction payload need only be in units of the physical sector size, and
 * as such we use buffer heads to co-ordinate cleaning and redirtying.
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
#define sector2offset(sect) ((sect) << HFSPLUS_SECTOR_SHIFT)

/*
 * Revised Flow:
 * current->journal_info = blist;
 * blist->info[1].block = bh->blocknr;
 * blist->info[1].bytes = sb->s_blocksize;
 * memcpy(bh->b_data, buffer);
 * bh->b_private = &blist->info[1];
 * bh->b_end_io = hfsplus_journal_finalize;
 * virt_to_page(blist)->private = virt_to_page(buffer);
 * bh->b_state |= BH_Lock; //suppress writeback; bh->b_page->flags & PG_Lock protects access
 * atomic_inc(bh->b_count);
 */

struct hfsplus_transact {
	unsigned char nesting;
	unsigned short bufferc;
	struct buffer_head *buffers;
	struct super_block *superblock;
};

static struct page *hfsplus_journal_read(struct hfsplus_sb_info *sbi);
static int hfsplus_journal_write(struct page *p);

static int hfsplus_journal_replay(struct hfsplus_sb_info *sbi);
static void hfsplus_cancel_log(void);
static void hfsplus_commit_log(struct buffer_head *, int); /* bh_end_io */
static void hfsplus_finish_log(struct buffer_head *, int); /* bh_end_io */

static __be32 hfsplus_checksum(const void *ptr, size_t len)
{
	int i;
	uint32_t res = 0;
	for (i = 0; i < len; ++i)
		res = (res << 8) ^ (res + ((char *)ptr)[i]);
	return cpu_to_be32(res);
}

/*
 * Safely synchronize journal. TODO: clean up old block lists, then data-sync
 * journal header, then buffer.
 */
static int hfsplus_journal_sync(struct super_block *sb, bool wait)
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

	sbi->journal_hdr->head = cpu_to_be64(sector2offset(sbi->journal_ptr));
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
 * Initialize and validate journaling subsystem
 */
int hfsplus_journal_init(struct hfsplus_sb_info *sbi)
{
	struct hfsplus_vh *vhdr = sbi->s_vhdr;
	struct hfsplus_jinfo *jinfo;
	struct hfsplus_jhdr *jhdr;
	struct page *page;
	__be32 chksum;

	/* verify journal metadata */
	page = do_read_cache_page(sbi->journal_info->i_mapping, 0,
				  sbi->journal_info->i_mapping->a_ops->readpage,
				  NULL, GFP_NOFS);
	if (!page || !(jinfo = kmap(page)))
		return -EIO;
	get_page(page);

	/* TODO: verify journal info block extent */

	page = do_read_cache_page(sbi->journal->i_mapping, 0,
				  sbi->journal->i_mapping->a_ops->readpage,
				  NULL, GFP_NOFS);
	if (!page || !(jhdr = kmap(page)))
		return -EIO;
	get_page(page);

	/* TODO: verify journal extent */

	if (!(be32_to_cpu(jinfo->flags) & HFSPLUS_JINFO_INTERNAL) ||
			be32_to_cpu(jinfo->flags) & HFSPLUS_JINFO_EXTERNAL) {
		/* the spec. says to reject external journals */
		pr_warn("external journal unsupported\n");
		return -ENOSYS;
	}

	if (be32_to_cpu(jinfo->flags) & HFSPLUS_JINFO_NEED_INIT) {
		/* initialize journal header */
		jhdr->magic = cpu_to_be32(HFSPLUS_JHDR_MAGIC);
		jhdr->endian = cpu_to_be32(HFSPLUS_JHDR_ENDIAN);
		jhdr->tail = jhdr->head = cpu_to_be64(sb->s_blocksize);
		jhdr->length = jinfo->length;
		jhdr->blist_sz = cpu_to_be32(sb->s_blocksize);
		jhdr->jhdr_sz = cpu_to_be32(sb->s_blocksize);
		jhdr->checksum = 0;
		jhdr->checksum = hfsplus_calc_chksum(jhdr,
						sizeof(struct hfsplus_jhdr));
		page = virt_to_page(jhdr);
		set_page_dirty(page);
		lock_page(page);
		error = write_one_page(page, true);
		if (!error) {
			jinfo->flags ^= cpu_to_be32(HFSPLUS_JINFO_NEED_INIT);
			page = virt_to_page(jinfo);
			set_page_dirty(page);
			lock_page(page);
			error = write_one_page(page, true);
		}
	}
	if (error)
		goto err;

	chksum = jhdr->checksum;
	jhdr->checksum = 0;
	jhdr->checksum = hfsplus_calc_chksum(jhdr, sizeof(struct hfsplus_jhdr));
	if (jhdr->checksum != chksum
			|| be32_to_cpu(jhdr->magic) != HFSPLUS_JHDR_MAGIC
			|| be32_to_cpu(jhdr->endian) != HFSPLUS_JHDR_ENDIAN) {
		/* journal header is corrupt */
		pr_crit("corrupt journal header on %s\n", sb->s_id);
		error = -EINVAL;
		goto err;
	}

	sbi->journal_hdr = jhdr;
	sbi->blcnt = (be32_to_cpu(jhdr->blsize) - sizeof(struct hfsplus_blhdr)) /
		      sizeof(struct hfsplus_blent);

	error = 0;
	goto out;
err:
	page = virt_to_page(jhdr);
	kunmap(page);
	put_page(page);
out:
	/* always free journal info block mapping, since it's useless now */
	page = virt_to_page(jinfo);
	kunmap(page);
	put_page(page);
	return error;
}

/*
 * Clean up journal
 */
int hfsplus_journal_exit(struct hfsplus_sb_info *sbi)
{
	struct page *pg;
	int error;

	error = hfsplus_journal_sync(sbi);

	pg = virt_to_page(sbi->journal_hdr);
	kunmap(pg);
	put_page(pg);

	iput(sbi->journal_info);
	iput(sbi->journal);

	return error;
}

/*
 * Read next (tail) page from journal.
 */
static struct page *hfsplus_journal_read(struct hfsplus_sb_info *sbi)
{
	struct hfsplus_jhdr *jh = sbi->journal_hdr;
	bool wrapa = be64_to_cpu(jh->tail) > be64_to_cpu(jh->head);
	struct page *p;
	p = do_read_cache_page(sbi->journal->i_mapping,
			       (be64_to_cpu(jh->size) +
			       	be64_to_cpu(jh->tail)) >> PAGE_CACHE_SHIFT,
			       sbi->journal->i_mapping->a_ops->readpage,
			       NULL, GFP_NOFS);
	BUG_ON(be64_to_cpu(jh->tail) == be64_to_cpu(jh->head)); /* read overflow */
	jh->tail = cpu_to_be64((be64_to_cpu(jh->tail) +
				PAGE_CACHE_SIZE) %
			       be64_to_cpu(jh->length));
	return p;
}

/*
 * Write next (head) page to journal.
 */
static void hfsplus_journal_write(struct hfsplus_sb_info *sbi, struct page *p)
{
	struct hfsplus_jhdr *jh = sbi->journal_hdr;
	int error;
	error = add_to_page_cache_locked(p, sbi->journal->i_mapping,
					 (be64_to_cpu(jh->size) +
					  be64_to_cpu(jh->head)) >>
					 PAGE_CACHE_SHIFT, GFP_NOFS);
	jh->head = cpu_to_be64((be64_to_cpu(jh->head) +
				PAGE_CACHE_SIZE) %
			       be64_to_cpu(jh->length));
	BUG_ON(be64_to_cpu(jh->tail) == be64_to_cpu(jh->head)); /* write overflow */
	return error;
}

/*
 * Replay any failed transactions in the journal, called only when cleaning
 * up a live filesystem. TODO: move to fsck.hfs
 */
int hfsplus_journal_replay(struct super_block *sb)
{
	struct hfsplus_sb_info *sbi = HFSPLUS_SB(sb);
	struct hfsplus_jhdr *jh = sbi->journal_hdr;
	struct hfsplus_blhdr *blist = NULL;
	struct bio *bio;
	void *blocks;
	const char *ptr;
	uint64_t blk;
	uint32_t len;
	uint16_t idx;
	int ret;

	if (jh->tail == jh->head)
		goto done;

	if (be64_to_cpu(jh->tail) % sb->s_blocksize) {
		pr_crit("ill-aligned journal on %s\n", sb->s_id);
		return -EINVAL;
	}

	pr_info("replaying journal on %s\n", sb->s_id);
	while (jh->tail != jh->head) {

		blist = kmap(hfsplus_journal_read(sbi));

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
		kfree(blist);
		kfree(blocks);

		/* try to update journal header (not critical) */
		hfsplus_journal_sync(sb, false);
	}

done:
	return hfsplus_journal_sync(sb, true);
}

/*
 * Begin recording a transaction.
 */
int hfsplus_journal_start(struct super_block *sb)
{
	struct hfsplus_transact *trans = current->journal_info;

	if (!is_journaled(sb))
		return 0; /* journaling disabled */

	if (trans) {
		trans->depth++;
		return 0;
	}

	current->journal_info = trans = kmalloc(sizeof *trans, GFP_NOFS);
	if (unlikely(!trans))
		return -ENOMEM;
	trans->nesting = 0;
	trans->superblock = sb;
	trans->bufferc = 0;
	trans->buffers = NULL;
	return 0;
}

/*
 * Queue dirtied buffers (locking them as well) in the ongoing transaction, to be
 * synched after it's been recorded in the journal, if journaling is active.
 */
int hfsplus_journal_page(struct page *page, off_t off, size_t len)
{
	set_page_dirty(page);

	if (!trans)
		return 0;

	if (trans->superblock != page->mapping->host->i_sb)
		return -EINVAL;

	return 0;
}

int hfsplus_journal_buffer(struct buffer_head *bh)
{
	struct hfsplus_transact *trans = current->journal_info;

	if (!is_journaled(sb))
		return 0;


	BUG_ON(trans->);
}

/*
 * Either cancel or commit the record depending on the success of the operation.
 */
int hfsplus_journal_stop(void)
{
	struct hfsplus_sb_info *sbi = HFSPLUS_SB(trans->superblock);
	struct hfsplus_transact *trans = current->journal_info;
	struct hfsplus_blhdr *blist;
	struct buffer_head *bh;
	uint64_t block;
	uint32_t bytes;
	unsigned dst, src = 0;

	if (!is_journaled(trans->superblock))
		return 0;

	BUG_ON(!trans);

	if (trans->depth) {
		trans->depth--;
		return 0;
	}

	current->journal_info = NULL;
	for (bh = trans->buffers; bh; bh = bh->private)
		;

	kfree(trans);
	return 0;
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
					(bytes >> trans->superblock->s_blocksize_bits);
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
	struct bvec_iter bi = { .bi_size = sector2offset(comm->length) };
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
	sbi->journal_hdr->head = cpu_to_be64(sector2offset(sbi->journal_cur));
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
 * FIXME: way better idea; just flag finalized transactions payloads as
 * skippable, then replay journal, doing nothing.
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
		hfsplus_sync_journal(bh->b_bdev->bd_super, false);
		/* now submit queued transactions */
		for (bio = sbi->journal_bio; bio; bio = bio->bi_next)
			hfsplus_submit_transact(bio, false);
	}

	mutex_unlock(&sbi->journal_mtx);

	end_buffer_async_write(bh, uptodate);

	return;
}