// SPDX-License-Identifier: GPL-2.0-only
#define pr_fmt(fmt) KBUILD_MODNAME ": " fmt
/*
 * Copyright (C) 2020-2022 Oplus. All rights reserved.
 */
#include <asm/pgtable-types.h>
#include <asm/pgalloc.h>
#include <linux/mm.h>
#include <linux/mman.h>
#include <linux/pagemap.h>
#include <linux/rmap.h>
#include <linux/init.h>
#include <linux/mmu_notifier.h>
#include <linux/gfp.h>
#include <linux/string.h>
#include <linux/mm_inline.h>
#include <linux/backing-dev.h>
#include <linux/proc_fs.h>
#include <linux/cpumask.h>
#include <linux/delay.h>
#include <linux/page_owner.h>
#include <uapi/linux/sched/types.h>

#include <linux/mm_types.h>
#include <linux/huge_mm.h>
#include <linux/shmem_fs.h>
#include <linux/cma.h>
#include <linux/memblock.h>
#include <linux/sched/mm.h>

#include "cma.h"
#include "internal.h"

#define endio_spinlock android_kabi_reserved2

#define M2N(SZ) (SZ / HPAGE_CONT_PTE_SIZE)
#define MAX_POOL_ALLOC_RETRIES (2)

DEFINE_STATIC_KEY_FALSE(cont_pte_huge_page_enabled_key);

struct cont_pte_huge_page_stat {
	/* reserved last index for alloc fail */
	atomic64_t alloc_retries[MAX_POOL_ALLOC_RETRIES + 1 + 1];
	atomic64_t direct_alloc[2];
	atomic64_t direct_alloc_fail[2];
};

struct huge_page_pool {
	int low, high, max, count;
	struct list_head item;
	spinlock_t spinlock;
	struct task_struct *refill_worker;
	int tot_count;
};

struct cont_pte_huge_page_stat perf_stat;
struct huge_page_pool cont_pte_huge_page_pool;

/* map up to 8 hugepages in case we are eligible for hugepage mapping */
#define MAX_HUGEPAGE_MAPAROUND 8
#define NR_FAULT_AROUND_STAT_ITEMS (MAX_HUGEPAGE_MAPAROUND + 1)

static atomic64_t fault_around_stat[NR_FAULT_AROUND_STAT_ITEMS] __cacheline_aligned_in_smp;

atomic_long_t cont_pte_double_map_count;

inline bool within_cont_pte_cma(unsigned long pfn)
{
	return cont_pte_cma && pfn >= cont_pte_cma->base_pfn &&
		pfn < cont_pte_cma->base_pfn + cont_pte_cma->count;
}

inline bool is_cont_pte_cma(struct cma *cma)
{
	return cma == cont_pte_cma;
}

inline bool transhuge_cont_pte_vma_suitable(struct vm_area_struct *vma,
						   unsigned long haddr)
{
	if (!vma_is_anonymous(vma)) {
		struct inode *inode;

		if (!vma->vm_file || !vma->vm_file->f_inode)
			return false;

		inode = vma->vm_file->f_inode;

		if (!S_ISREG(inode->i_mode))
			return false;

		if (!inode->may_cont_pte)
			return false;

		/* vm_account means the vma was for writing */
		if (vma->vm_flags & (VM_WRITE | VM_ACCOUNT))
			return false;

		if (shmem_file(vma->vm_file))
			return false;

		if (!transhuge_cont_pte_vma_aligned(vma))
			return false;

		if (inode_is_open_for_write(inode))
			return false;

		return transhuge_cont_pte_addr_suitable(vma, haddr);
	}

	return false;
}

static inline bool is_cont_pte_cma_full(void);

int read_huge_page_pool_pages(void)
{
	return (cont_pte_huge_page_pool.count) * HPAGE_CONT_PTE_NR;
}

static inline struct page *huge_page_pool_alloc_pages(void)
{
	struct page *page;
	int i;
	struct huge_page_pool *pool = &cont_pte_huge_page_pool;

	/*
	 * at the boot stage, buddy is likely to have 4-order memory.
	 * some of them might be mlocked or permanently hot in LRU.
	 * so we try to get memory from buddy and easy the runtime
	 * pressure for cma. In rush hour of launching apps using lots
	 * of hugpages, they are easier to get 64KB pages from cma
	 */
	if (pool->max) {
		page = alloc_pages((GFP_HIGHUSER | __GFP_ZERO | __GFP_NOWARN |
					__GFP_NORETRY) & ~__GFP_RECLAIM, HPAGE_CONT_PTE_ORDER);
		if (page) {
			split_page(page, HPAGE_CONT_PTE_ORDER);
			goto out;
		}
	}

	page = cma_alloc(cont_pte_cma, 1 << HPAGE_CONT_PTE_ORDER, HPAGE_CONT_PTE_ORDER,
			 GFP_KERNEL | __GFP_NOWARN);
	if (page)
		goto out;

	page = alloc_pages((GFP_HIGHUSER | __GFP_ZERO | __GFP_NOWARN |
			   __GFP_NORETRY) & ~__GFP_RECLAIM, HPAGE_CONT_PTE_ORDER);
	if (page)
		split_page(page, HPAGE_CONT_PTE_ORDER);

out:
	if (page) {
		/* alloc pages only set the 1st page's private to 0 */
		for (i = 0; i < HPAGE_CONT_PTE_NR; i++)
			set_page_private(&page[i], 0);
	}

	return page;
}

static void huge_page_pool_add(struct page *page, bool refill)
{
	struct huge_page_pool *pool = &cont_pte_huge_page_pool;

#ifdef CONFIG_CONT_PTE_HUGEPAGE_DEBUG_VERBOSE
	int i;

	for (i = 0; i < HPAGE_CONT_PTE_NR; i++) {
		BUG_ON(atomic_read(&page[i]._refcount) != 1 && !refill);
		BUG_ON(atomic_read(&page[i]._mapcount) + 1);
		BUG_ON(PageCompound(&page[i]));
		WARN_ON_ONCE(page[i].flags); /* some new pages have 4000 0000 0000 0000, why? */
		WARN_ON_ONCE(page[i].private);
	}
#endif

	spin_lock(&pool->spinlock);
	/* re-mark this so that cma_release can skip clearing bitmap */
	if (refill)
		SetPageCont(page);
	list_add_tail(&page->lru, &pool->item);
	pool->count++;
	spin_unlock(&pool->spinlock);
}

bool huge_page_pool_refill(struct page *page)
{
	struct huge_page_pool *pool = &cont_pte_huge_page_pool;

	if (pool->count >= pool->high)
		return false;

	BUG_ON(!IS_ALIGNED(page_to_pfn(page), HPAGE_CONT_PTE_NR));

	huge_page_pool_add(page, true);
	return true;
}

static struct page *huge_page_pool_remove(void)
{
	struct huge_page_pool *pool = &cont_pte_huge_page_pool;
	struct page *page;
	int i;

	spin_lock(&pool->spinlock);
	page = list_first_entry_or_null(&pool->item, struct page, lru);
	if (page) {
		pool->count--;
		list_del(&page->lru);
	}
	spin_unlock(&pool->spinlock);

	if (pool->count < pool->low)
		wake_up_process(pool->refill_worker);

	/* a refilled hugepage from free_compound_page */
	if (page && PageCont(page)) {
		for (i = 0; i < HPAGE_CONT_PTE_NR; i++)
			post_alloc_hook(&page[i], 0, GFP_KERNEL);
	}

	return page;
}

static int huge_page_pool_refill_worker(void *data)
{
	struct huge_page_pool *pool = data;
	struct page *page;
	s64 time;
	int expect, i, retries, max_retries = 100;

	for (;;) {
		time = ktime_to_ms(ktime_get());
		expect = pool->max ?: pool->high;
		expect = max(expect - pool->count, 0);
		retries = i = 0;

		while (i < expect) {
			if (!pool->max && pool->count >= pool->high)
				break;

			page = huge_page_pool_alloc_pages();
			if (!page) {
				if (retries++ >= max_retries) {
					pr_err("refill page timeout\n");
					break;
				}

				set_current_state(TASK_INTERRUPTIBLE);
				schedule_timeout(msecs_to_jiffies(20));
				continue;
			}

			huge_page_pool_add(page, false);
			retries = 0;
			i++;
		}

		if (unlikely(pool->max))
			pool->max = 0;

		pr_info("%s prealloc expect: %d fact: %d cur: %d, completed in %lldms...\n",
			__func__, expect, i, pool->count,
			ktime_to_ms(ktime_get()) - time);

		set_current_state(TASK_INTERRUPTIBLE);
		if (unlikely(kthread_should_stop())) {
			set_current_state(TASK_RUNNING);
			break;
		}
		schedule();

		set_current_state(TASK_RUNNING);
	}
	return 0;
}

static struct page *alloc_cont_pte_hugepage(void)
{
	struct page *page = NULL;
	int retries = 0;
	static bool first_alloc = true;
	bool enable_direct_alloc = false;

	if (unlikely(first_alloc)) {
		pr_info("%s: Initial hugepage pool size: %lu MiB\n", __func__,
			cont_pte_huge_page_pool.count * HPAGE_CONT_PTE_SIZE / SZ_1M);
		first_alloc = false;
	}

retry:
	page = huge_page_pool_remove();

	/* enter slow path */
	if (!page && enable_direct_alloc) {
		unsigned long long start, end;
		int inx = 0;
		atomic64_t *arr;

		start = sched_clock();
		page = huge_page_pool_alloc_pages();
		end = sched_clock();

		/* over than 64ms */
		if (end - start > 64000000ULL) {
			pr_warn_ratelimited("%s %s:%d direct alloc usage %lld, ret: %d\n",
					    __func__, current->comm, current->tgid,
					    end - start, !!page);
			inx = 1;
		}
		arr = page ? perf_stat.direct_alloc : perf_stat.direct_alloc_fail;

		atomic64_add(1, arr + inx);
	}

	/* wait for a sec */
	if (!page) {
		if (is_cont_pte_cma_full()) {
			retries = MAX_POOL_ALLOC_RETRIES + 1;
			goto out;
		}

		if (retries < MAX_POOL_ALLOC_RETRIES) {
			retries++;
			set_current_state(TASK_INTERRUPTIBLE);
			schedule_timeout(msecs_to_jiffies(16));
			goto retry;
		}

		retries++;
		pr_err_ratelimited("%s FIXME: %s %d Failed to alloc cont-pte pages\n",
				   __func__, current->comm, current->pid);
	}
out:
	atomic64_add(1, perf_stat.alloc_retries + retries);
	return page;
}

/**********************from *arch/arm64/mm/hugetlbpage.c******************************************/

static pte_t get_clear_flush(struct mm_struct *mm,
			     unsigned long addr,
			     pte_t *ptep,
			     unsigned long pgsize,
			     unsigned long ncontig,
			     bool flush)
{
	pte_t orig_pte = ptep_get(ptep);
	bool valid = pte_valid(orig_pte);
	unsigned long i, saddr = addr;

	for (i = 0; i < ncontig; i++, addr += pgsize, ptep++) {
		pte_t pte = ptep_get_and_clear(mm, addr, ptep);

		WARN_ON(pte_dirty(pte));

		if (pte_young(pte))
			orig_pte = pte_mkyoung(orig_pte);
	}

	if (valid && flush) {
		struct vm_area_struct vma = TLB_FLUSH_VMA(mm, 0);

		flush_tlb_range(&vma, saddr, addr);
	}
	return orig_pte;
}

/*
 * Select all bits except the pfn
 */
static inline pgprot_t pte_pgprot(pte_t pte)
{
	unsigned long pfn = pte_pfn(pte);

	return __pgprot(pte_val(pfn_pte(pfn, __pgprot(0))) ^ pte_val(pte));
}

static inline pte_t __cont_pte_huge_ptep_get_and_clear_flush(struct mm_struct *mm,
				       unsigned long addr,
				       pte_t *ptep,
				       bool flush)
{
	pte_t orig_pte = ptep_get(ptep);

	BUG_ON(!pte_cont(orig_pte));
	BUG_ON(!IS_ALIGNED(addr, HPAGE_CONT_PTE_SIZE));
	BUG_ON(!IS_ALIGNED(pte_pfn(orig_pte), HPAGE_CONT_PTE_NR));

	return get_clear_flush(mm, addr, ptep, PAGE_SIZE, CONT_PTES, flush);
}

pte_t cont_pte_huge_ptep_get_and_clear_flush(struct mm_struct *mm,
					     unsigned long addr,
					     pte_t *ptep)
{
	return __cont_pte_huge_ptep_get_and_clear_flush(mm, addr, ptep, true);
}

pte_t cont_pte_huge_ptep_get_and_clear(struct mm_struct *mm,
				       unsigned long addr,
				       pte_t *ptep)
{
	return __cont_pte_huge_ptep_get_and_clear_flush(mm, addr, ptep, false);
}

static void clear_flush(struct mm_struct *mm,
			unsigned long addr,
			pte_t *ptep,
			unsigned long pgsize, unsigned long ncontig)
{
	struct vm_area_struct vma = TLB_FLUSH_VMA(mm, 0);
	unsigned long i, saddr = addr;

	for (i = 0; i < ncontig; i++, addr += pgsize, ptep++)
		pte_clear(mm, addr, ptep);

	flush_tlb_range(&vma, saddr, addr);
}

void cont_pte_set_huge_pte_at(struct mm_struct *mm, unsigned long addr,
			      pte_t *ptep, pte_t pte)
{
	size_t pgsize = PAGE_SIZE;
	int i;
	unsigned long pfn, dpfn;
	pgprot_t hugeprot;

	pfn = pte_pfn(pte);
	dpfn = pgsize >> PAGE_SHIFT;
	hugeprot = pte_pgprot(pte);

	BUG_ON(!IS_ALIGNED(pfn, HPAGE_CONT_PTE_NR));
	BUG_ON(!IS_ALIGNED(addr, HPAGE_CONT_PTE_SIZE));
	BUG_ON(!pte_cont(pte));

	clear_flush(mm, addr, ptep, pgsize, CONT_PTES);

	for (i = 0; i < CONT_PTES; i++, ptep++, addr += pgsize, pfn += dpfn)
		set_pte_at(mm, addr, ptep, pfn_pte(pfn, hugeprot));
}

static inline void __do_set_cont_pte_with_addr(struct vm_fault *vmf,
		struct page *page,
		unsigned long addr)
{
	pte_t entry;
	struct vm_area_struct *vma = vmf->vma;
	unsigned long haddr = ALIGN_DOWN(addr, HPAGE_CONT_PTE_SIZE);
	pte_t *ptep = vmf->pte - (addr - haddr) / PAGE_SIZE;

	entry = mk_pte(page, vma->vm_page_prot);
	entry = pte_mkyoung(entry);
	entry = pte_mkcont(entry);

	add_mm_counter(vma->vm_mm, mm_counter_file(page), HPAGE_CONT_PTE_NR);
	page_add_file_rmap(page, true);

	cont_pte_set_huge_pte_at(vma->vm_mm, haddr, ptep, entry);

	count_vm_event(THP_FILE_MAPPED);
}

void do_set_cont_pte(struct vm_fault *vmf, struct page *page)
{
	__do_set_cont_pte_with_addr(vmf, page, vmf->address);
}

void do_set_cont_pte_with_addr(struct vm_fault *vmf,
			       struct page *page,
			       unsigned long addr)
{
	__do_set_cont_pte_with_addr(vmf, page, addr);
}

void __split_huge_cont_pte(struct vm_area_struct *vma, pte_t *pte,
			   unsigned long address, bool freeze,
			   struct page *page)
{
	struct mm_struct *mm = vma->vm_mm;
	struct page *head = compound_head(pte_page(*pte));
	unsigned long haddr = address & HPAGE_CONT_PTE_MASK;

	BUG_ON(page && (page != head));

#define THP_SPLIT_CONT_PTE THP_SPLIT_PMD	/* we are leveraging PMD count for CONT_PTE */
	count_vm_event(THP_SPLIT_CONT_PTE);

	if (!vma_is_anonymous(vma)) {
		cont_pte_huge_ptep_get_and_clear_flush(vma->vm_mm, haddr,
						       pte - (address - haddr) / PAGE_SIZE);
		page_remove_rmap(head, true);
		put_page(head);
		add_mm_counter(mm, mm_counter_file(head), -HPAGE_CONT_PTE_NR);
		return;
	}
}

void change_huge_cont_pte(struct vm_area_struct *vma, pte_t *pte,
			  unsigned long addr, pgprot_t newprot,
			  unsigned long cp_flags)
{
	struct mm_struct *mm = vma->vm_mm;
	pte_t oldpte, ptent;

	oldpte = cont_pte_huge_ptep_get_and_clear(mm, addr, pte);

	ptent = pte_modify(oldpte, newprot);

	cont_pte_set_huge_pte_at(mm, addr, pte, ptent);
}

void split_huge_cont_pte_address(struct vm_area_struct *vma,
				 unsigned long address,
				 bool freeze, struct page *page)
{
	if (!vma_is_anonymous(vma)) {
		unsigned long haddr = address & HPAGE_CONT_PTE_MASK;
		struct mmu_notifier_range range;
		spinlock_t *ptl;
		pgd_t *pgdp;
		p4d_t *p4dp;
		pud_t *pudp;
		pmd_t *pmdp;
		pte_t *ptep;

		if (vma_is_special_huge(vma))
			return;

		pgdp = pgd_offset(vma->vm_mm, haddr);
		if (!pgd_present(*pgdp))
			return;

		p4dp = p4d_offset(pgdp, haddr);
		if (!p4d_present(*p4dp))
			return;

		pudp = pud_offset(p4dp, haddr);
		if (!pud_present(*pudp))
			return;

		pmdp = pmd_offset(pudp, haddr);
		if (!pmd_present(*pmdp))
			return;

		ptep = pte_offset_map(pmdp, haddr);
		if (!pte_present(*ptep))
			return;

		mmu_notifier_range_init(&range, MMU_NOTIFY_CLEAR, 0, vma, vma->vm_mm,
				haddr, haddr + HPAGE_CONT_PTE_SIZE);
		mmu_notifier_invalidate_range_start(&range);

		ptl = pte_lockptr(vma->vm_mm, pmdp);
		spin_lock(ptl);
		/*
		 * NOTE: After obtaining the pte lock we need
		 * to check the pte again!
		 */
		if (!pte_cont(*ptep) || (page && page != pte_page(*ptep)))
			goto out;
		/* FIXME: Probes whether all 16 ptes are pte_cont */
		BUG_ON(!cont_pte_trans_huge(ptep));
		__split_huge_cont_pte(vma, ptep, haddr, freeze, page);

out:
		spin_unlock(ptl);

		mmu_notifier_invalidate_range_only_end(&range);
	}
}

static struct page *build_cont_pte_thp(struct address_space *mapping,
				struct page *page)
{
	int i;

	XA_STATE_ORDER(xas, &mapping->i_pages, page->index,
			HPAGE_CONT_PTE_ORDER);

	mapping_set_update(&xas, mapping);

	spin_lock_irq(&mapping->i_pages.xa_lock);
	if (!PageHead(page)) {
#ifdef CONFIG_CONT_PTE_HUGEPAGE_DEBUG_VERBOSE
		/* if there are mapped basepages, we fallback to basepage */
		for (i = 0; i < HPAGE_CONT_PTE_NR; i++) {
			if (atomic_read(&page[i]._mapcount) != -1) {
				pr_err("@ FIXME: _mapcount!=-1  %s:%d _mapcount=%d paref%lx !!!@\n",
				     __func__, __LINE__,
				     atomic_read(&page[i]._mapcount),
				     (unsigned long)&page[i]);
				BUG_ON(1);
				spin_unlock_irq(&mapping->i_pages.xa_lock);
				return ERR_PTR(-EBUSY);
			}
			if (atomic_read(&page[i]._refcount) < 1) {
				pr_err("@ FIXME: _refcount < 1  %s:%d _refcount=%d page=%lx pfn:%lx cma:%d !!!@\n",
				     __func__, __LINE__,
				     atomic_read(&page[i]._refcount),
				     (unsigned long)&page[i],
				     page_to_pfn(&page[i]),
				     within_cont_pte_cma(page_to_pfn(&page[i])));
				BUG_ON(1);
				spin_unlock_irq(&mapping->i_pages.xa_lock);
				return ERR_PTR(-EBUSY);
			}
		}
#endif
		get_page(page);
		prep_compound_page(page, HPAGE_CONT_PTE_ORDER);
		prep_transhuge_page(page);

		/* The reference count for all sub-pages is moved to the head page */
		page_ref_add(page, HPAGE_CONT_PTE_NR - 1);
		/*
		 * 5.10 set subpages' refcount to 0 in prep_compound_page,
		 * but 5.15 doesn't
		 */
		for (i = 1; i < HPAGE_CONT_PTE_NR; i++)
			page_ref_add_unless(&page[i], -1, 0);

		__inc_node_page_state(page, NR_FILE_THPS);
		__mod_lruvec_page_state(page, NR_FILE_PAGES, HPAGE_CONT_PTE_NR);
		xas_store(&xas, page);
		spin_unlock_irq(&mapping->i_pages.xa_lock);

		filemap_nr_thps_inc(mapping);
		lru_cache_add(page);

		count_vm_event(THP_FAULT_ALLOC);
	} else {
		spin_unlock_irq(&mapping->i_pages.xa_lock);
		pr_err("@@@FIXME: endio on THP %s page:%pK pfn:%lx flags:%lx\n",
			__func__, page, page_to_pfn(page), page->flags);
	}

	return page;
}

static struct page *find_get_entry_nolocked(struct address_space *mapping,
					    pgoff_t index)
{
	XA_STATE(xas, &mapping->i_pages, index);
	struct page *page;

 repeat:
	xas_reset(&xas);
	page = xas_load(&xas);
	if (xas_retry(&xas, page))
		goto repeat;

	if (!page || xa_is_value(page))
		goto out;

	if (!page_cache_get_speculative(page))
		goto repeat;

	if (unlikely(page != xas_reload(&xas))) {
		put_page(page);
		goto repeat;
	}
 out:
	return page;
}

/* return head if xa has cont_pte pages, otherwise, return the page in index */
struct page *find_get_entry_may_cont_pte(struct address_space *mapping,
		pgoff_t index)
{
	pgoff_t head = ALIGN_DOWN(index, HPAGE_CONT_PTE_NR);
	struct page *page;

	spin_lock_irq(&mapping->i_pages.xa_lock);
	page = find_get_entry_nolocked(mapping, head);

	/* we happen to search the head, no matter what it is, return */
	if (head == index)
		goto out;

	/* we get nothing at head, further search the exact index */
	if (!page || xa_is_value(page)) {
		page = find_get_entry_nolocked(mapping, index);
		goto out;
	}

	if (!PageCont(page)) {
		/* head is an ordinary page, search the exact index */
		put_page(page);
		page = find_get_entry_nolocked(mapping, index);
	}

out:
	spin_unlock_irq(&mapping->i_pages.xa_lock);

	/* almost always true */
	if (page && !xa_is_value(page) && likely(!in_atomic()))
		wait_on_page_locked(page);
	/* almost always false, to be compatible with potential atomic context */
	while (page && !xa_is_value(page) && PageCont(page) && !PageTransCompound(page))
		cpu_relax();
	BUG_ON(page && !xa_is_value(page) && PageCont(page) && !PageHead(page));

	return page;
}

static struct page *find_get_page_nolocked(struct address_space *mapping,
					   pgoff_t offset)
{
	struct page *page;

	page = find_get_entry_nolocked(mapping, offset);
	if (xa_is_value(page))
		page = NULL;

	if (!page)
		return NULL;

	page = find_subpage(page, offset);

	return page;
}

static int __find_get_cont_pte_pages(struct address_space *mapping, pgoff_t offset,
		struct page **ret_page)
{
	int i;
	struct page *page;
	pgoff_t start = ALIGN_DOWN(offset, HPAGE_CONT_PTE_NR);
	*ret_page = NULL;

	for (i = 0; i < HPAGE_CONT_PTE_NR; i++) {
		if (i == 0) {
			page = find_get_page_nolocked(mapping, start);
			if (!page)
				continue;
			if (ContPteHugePageHead(page)) {
				*ret_page = page;
				return HIT_THP;
			} else if (PageCont(page)) {
				*ret_page = page;
				return HIT_CONT;
			}

			if (start == offset) {
				*ret_page = page;
				return HIT_BASEPAGE;
			} else {
				put_page(page);
				*ret_page = find_get_page_nolocked(mapping, offset);
				return HIT_BASEPAGE;
			}
		} else {
			page = find_get_page_nolocked(mapping, start + i);

			if (page) {
				if (start + i == offset) {
					*ret_page = page;
					return HIT_BASEPAGE;
				}

				put_page(page);
				if (start + i < offset)
					*ret_page = find_get_page_nolocked(mapping, offset);
				return HIT_BASEPAGE;
			}
		}
	}

	return HIT_NOTHING;
}


/* return either the head page(if hit cont_pte) or the basepage located at offset */
int find_get_cont_pte_pages(struct address_space *mapping, pgoff_t offset,
		struct page **ret_page)
{
	int ret;

	spin_lock_irq(&mapping->i_pages.xa_lock);
	ret = __find_get_cont_pte_pages(mapping, offset, ret_page);
	spin_unlock_irq(&mapping->i_pages.xa_lock);

	return ret;
}

static int cont_add_to_page_cache_locked(struct page *page,
					   struct address_space *mapping,
					   pgoff_t offset, gfp_t gfp,
					   void **shadowp)
{
	XA_STATE(xas, &mapping->i_pages, offset);
	unsigned int order;
	void *entry, *old = NULL;
	int error;
	int i, j;

	mapping_set_update(&xas, mapping);

	xas_set_order(&xas, offset, HPAGE_CONT_PTE_ORDER);
	do {
		xas_lock_irq(&xas);
		xas_create_range(&xas);
		if (!xas_error(&xas))
			break;
		xas_unlock_irq(&xas);
		if (!xas_nomem(&xas, GFP_KERNEL)) {
			pr_err("%s %d EINVAL start:%lx mapping:%lx", __func__, __LINE__,
				(unsigned long)offset, (unsigned long)mapping);
			return -EINVAL;
		}
	} while (1);
	xas_unlock_irq(&xas);

	gfp &= GFP_RECLAIM_MASK;
	for (i = 0; i < HPAGE_CONT_PTE_NR; i++) {
		xas_set_order(&xas, offset + i, 0);

		get_page(&page[i]);
		page[i].mapping = mapping;
		page[i].index = offset + i;

		order = xa_get_order(xas.xa, xas.xa_index);
		/* Allocate memory for splitting an entry */
		if (order > thp_order(&page[i]))
			xas_split_alloc(&xas, xa_load(xas.xa, xas.xa_index),
					order, gfp);
	}

	xas_lock_irq(&xas);

	/* make sure all of 16 entries are empty before inserting */
	do {
		struct page *page;
		int ret = __find_get_cont_pte_pages(mapping, ALIGN_DOWN(offset, HPAGE_CONT_PTE_NR), &page);

		j = 0;
		if (page)
			put_page(page);
		if (ret != HIT_NOTHING) {
			xas_set_err(&xas, -EEXIST);
			goto error;
		}
	} while (0);

	for (j = 0; j < HPAGE_CONT_PTE_NR; j++) {
		xas_set_order(&xas, offset + j, 0);
		xas_for_each_conflict(&xas, entry) {
			old = entry;
			/*
			 * NOTE: Only get the shadow of the header
			 * entry for cont-pte huegpage workingset!
			 */
			if (!j && shadowp)
				*shadowp = old;
			if (!xa_is_value(entry)) {
				xas_set_err(&xas, -EEXIST);
				pr_err("%s %d EEXIST start:%lx off:%d mapping:%lx  old=%lx PageCompound=%d PageCont=%d PageHead=%d\n",
						__func__, __LINE__, (unsigned long)offset, j, (unsigned long)mapping,
						(unsigned long)old, PageCompound((struct page *)old),
						PageCont((struct page *)old), PageHead((struct page *)old));
				BUG_ON(1);
				goto error;
			}
		}

		if (old) {
			/* entry may have been split before we acquired lock */
			order = xa_get_order(xas.xa, xas.xa_index);
			if (order > thp_order(&page[j])) {
				/*  NOTE: Split a multi-index entry into smaller entries */
				xas_split(&xas, old, order);
				xas_reset(&xas);
			}
		}

		xas_store(&xas, &page[j]);
		if (xas_error(&xas)) {
			pr_err("@%s:%d FIXME: Failed to xas_store @\n", __func__, __LINE__);
			goto error;
		}
		mapping->nrpages++;
	}

error:
	if (xas_error(&xas)) {
		error = xas_error(&xas);

		if (j) {
			for (j--; j >= 0; j--) {
				xas_set(&xas, offset + j);
				xas_store(&xas, NULL);
				xas_init_marks(&xas);
				mapping->nrpages--;
			}
		}
		xas_unlock_irq(&xas);

		for (i = 0; i < HPAGE_CONT_PTE_NR; i++) {
			page[i].mapping = NULL;
			/* Leave page->index set: truncation relies upon it */
			put_page(&page[i]);
		}

		return error;
	}

	xas_unlock_irq(&xas);
	return 0;
}

static bool alloc_contpages_and_add_xa(struct address_space *mapping,
		      unsigned long index,
		      gfp_t gfp_mask,
		      struct list_head *page_pool, struct page **ret_page)
{
	int i;
	struct page *page;
	void *shadow = NULL;
	struct huge_page_pool *pool = &cont_pte_huge_page_pool;
	int ret;

	/*
	 * we only support fs without readpages which are real for
	 * ext4, erofs and f2fs
	 */
	BUG_ON(mapping->a_ops->readpages);

	page = alloc_cont_pte_hugepage();
	if (!page)
		goto fail_alloc;

	for (i = 0; i < HPAGE_CONT_PTE_NR; i++) {
		/* FIXME: we need this before we fix endio on THP */
		ClearPageContUptodate(&page[i]);
		ClearPageContIODoing(&page[i]);
		SetPageCont(&page[i]);
		__SetPageLocked(&page[i]);
	}

	if (unlikely(mem_cgroup_charge(page, NULL, gfp_mask))) {
		pr_err("@%s:%d mem_cgroup_charge\n", __func__, __LINE__);
		goto fail_charge;
	}

	ret = cont_add_to_page_cache_locked(page, mapping, index, gfp_mask, &shadow);
	if (ret < 0) {
		goto fail_xa;
	} else {
		/* NOTE: just do workingset for header page! */
		WARN_ON_ONCE(PageActive(page));
		if (!(gfp_mask & __GFP_WRITE) && shadow)
			workingset_refault(page, shadow);
	}

	*ret_page = page;
	return true;
fail_xa:
	mem_cgroup_uncharge(page);
fail_charge:
	for (i = 0; i < HPAGE_CONT_PTE_NR; i++) {
		__ClearPageLocked(&page[i]);
		ClearPageCont(&page[i]);
	}

	/* try to refill pool before releasing */
	if (within_cont_pte_cma(page_to_pfn(page)) && pool->count < pool->high) {
		huge_page_pool_add(page, false);
	} else if (!cma_release(cont_pte_cma, page, 1 << HPAGE_CONT_PTE_ORDER)) {
		for (i = 0; i < HPAGE_CONT_PTE_NR; i++)
			__free_page(&page[i]);
	}

fail_alloc:
	*ret_page = NULL;
	return false;
}

static void read_pages(struct readahead_control *rac,
		       struct list_head *pages, bool skip_page)
{
	const struct address_space_operations *aops = rac->mapping->a_ops;
	struct page *page;
	struct blk_plug plug;

	if (!readahead_count(rac))
		goto out;

	blk_start_plug(&plug);

	if (aops->readahead) {
		aops->readahead(rac);
		/* Clean up the remaining pages */
		while ((page = readahead_page(rac))) {
			if (PageCont(page)) {
				pr_err("@@@FIXME: %s readahead_page page:%pK pfn:%lx flags:%lx ref:%d index:%lx process:%s %d compound_head:%lx %pK cma:%d\n",
						__func__, page, page_to_pfn(page), page->flags, atomic_read(&page->_refcount),
						page->index, current->comm, current->pid, page->compound_head, compound_head(page),
						within_cont_pte_cma(page_to_pfn(page)));
				dump_page(page, "THP readahead_page");
				dump_page(compound_head(page), "THP readahead_page head");
				BUG_ON(1);
			}
			unlock_page(page);
			put_page(page);
		}
	} else if (aops->readpages) {
		aops->readpages(rac->file, rac->mapping, pages,
				readahead_count(rac));
		/* Clean up the remaining pages */
		put_pages_list(pages);
		rac->_index += rac->_nr_pages;
		rac->_nr_pages = 0;
	} else {
		while ((page = readahead_page(rac))) {
			aops->readpage(rac->file, page);
			put_page(page);
		}
	}

	blk_finish_plug(&plug);

	BUG_ON(!list_empty(pages));
	BUG_ON(readahead_count(rac));

 out:
	if (skip_page)
		rac->_index++;
}

static void cont_pte_hugepage_ra(struct readahead_control *ractl,
					   unsigned long nr_to_read,
					   unsigned long lookahead_size,
					   struct vm_fault *vmf)
{
	unsigned long i;
	struct address_space *mapping = ractl->mapping;
	unsigned long index = readahead_index(ractl);
	LIST_HEAD(page_pool);
	gfp_t gfp_mask = readahead_gfp_mask(mapping);
	int ret;
	unsigned int nofs = memalloc_nofs_save();

	for (i = 0; i < nr_to_read; i += HPAGE_CONT_PTE_NR) {
		struct page *page = NULL;

		ret = find_get_cont_pte_pages(mapping, index + i, &page);
		if (ret != HIT_NOTHING) {
			if (page)
				put_page(page);

			read_pages(ractl, &page_pool, false);
			ractl->_index = index + i + HPAGE_CONT_PTE_NR;
			ractl->_nr_pages = 0;
			continue;
		}

		ret = alloc_contpages_and_add_xa(mapping, index + i, gfp_mask, &page_pool,
				     &page);
		if (!ret) {
			read_pages(ractl, &page_pool, false);
			ractl->_index = index + i + HPAGE_CONT_PTE_NR;
			ractl->_nr_pages = 0;
			continue;
		}

		/* Set the read-ahead flag for the last hugepage */
		if (i == nr_to_read - HPAGE_CONT_PTE_NR)
			SetPageReadahead(page);

		ractl->_nr_pages += HPAGE_CONT_PTE_NR;
	}

	read_pages(ractl, &page_pool, false);
	memalloc_nofs_restore(nofs);
}

struct file *do_cont_pte_sync_mmap_readahead(struct vm_fault *vmf)
{
	struct file *file = vmf->vma->vm_file;
	struct file_ra_state *ra = &file->f_ra;
	struct address_space *mapping = file->f_mapping;
	unsigned long haddr = vmf->address & HPAGE_CONT_PTE_MASK;
	DEFINE_READAHEAD(ractl, file, mapping, vmf->pgoff);
	struct file *fpin = NULL;

	fpin = maybe_unlock_mmap_for_io(vmf, fpin);

	if (vmf->address <= haddr + HPAGE_CONT_PTE_SIZE / 2) {
		/* Readahead a hugepage forward */
		if (haddr - HPAGE_CONT_PTE_SIZE < vmf->vma->vm_start)
			goto no_readahead;
		ra->start = ALIGN_DOWN(vmf->pgoff, HPAGE_CONT_PTE_NR) - HPAGE_CONT_PTE_NR;
	} else {
		/* Readahead a hugepage backwards */
		if (haddr + 2 * HPAGE_CONT_PTE_SIZE > vmf->vma->vm_end)
			goto no_readahead;
		ra->start = ALIGN_DOWN(vmf->pgoff, HPAGE_CONT_PTE_NR);
	}
	ra->size = 2 * HPAGE_CONT_PTE_NR;
	ra->async_size = 0;	/* we are ignoring it */
	ractl._index = ra->start;

	cont_pte_hugepage_ra(&ractl, ra->size, ra->async_size, vmf);
	return fpin;
 no_readahead:
	ractl._index = ALIGN_DOWN(vmf->pgoff, HPAGE_CONT_PTE_NR);
	ra->size = HPAGE_CONT_PTE_NR;
	ra->async_size = 0;
	cont_pte_hugepage_ra(&ractl, ra->size, ra->async_size, vmf);

	return fpin;
}

struct file *do_cont_pte_async_mmap_readahead(struct vm_fault *vmf, struct page *page)
{
	struct file *file = vmf->vma->vm_file;
	struct file_ra_state *ra = &file->f_ra;
	struct address_space *mapping = file->f_mapping;
	unsigned long haddr = vmf->address & HPAGE_CONT_PTE_MASK;
	DEFINE_READAHEAD(ractl, file, mapping, vmf->pgoff);
	struct file *fpin = NULL;
	unsigned int size = 0;
	int i;

	BUG_ON(PageWriteback(page));

	ClearPageReadahead(page);

	if (inode_read_congested(mapping->host))
		return fpin;

	if (blk_cgroup_congested())
		return fpin;

	if (haddr + 2 * HPAGE_CONT_PTE_SIZE > vmf->vma->vm_end)
		goto out;

	fpin = maybe_unlock_mmap_for_io(vmf, fpin);

	/* we read up to 3 hugepages */
	for (i = 0; i < 3; i++) {
		if (haddr + (i + 2) * HPAGE_CONT_PTE_SIZE > vmf->vma->vm_end)
			break;
		size += HPAGE_CONT_PTE_NR;
	}

	ra->start = ALIGN_DOWN(vmf->pgoff, HPAGE_CONT_PTE_NR) + HPAGE_CONT_PTE_NR;
	ra->size = size;
	ra->async_size = 0;	/* we are ignoring it */
	ractl._index = ra->start;
	cont_pte_hugepage_ra(&ractl, ra->size, ra->async_size, vmf);

out:
	return fpin;
}

static inline void __build_thp(struct address_space *mapping, struct page *head)
{
	bool error = TestClearPageError(head);
	int i;

	if (!error)
		goto done;

	/* we defer 150ms and re-read pages with IO errors */
	for (i = PG_cont_ioredo_s; i <= PG_cont_ioredo_e; i++) {
		if (test_and_set_bit(i, &head->flags))
			continue;
		msleep(150);
		break;
	}
	/* we have used up our retries, HW probably has broken */
	if (i > PG_cont_ioredo_e)
		goto done;

	for (i = 0; i < HPAGE_CONT_PTE_NR; i++)
		ClearPageContIODoing(&head[i]);

	for (i = 0; i < HPAGE_CONT_PTE_NR; i++) {
		/*
		 * if fs is struggling with getting memory, memory reclamation might
		 * need long time to be done, give retry one more chance
		 */
		if (mapping->a_ops->readpage(NULL, &head[i]) == -ENOMEM)
			clear_bit(PG_cont_ioredo_s, &head->flags);
	}
	return;

done:
	build_cont_pte_thp(mapping, head);
	if (!error) {
		for (i = PG_cont_ioredo_s; i <= PG_cont_ioredo_e; i++)
			clear_bit(i, &head->flags);
		SetPageUptodate(head);
	} else {
		ClearPageUptodate(head);
		SetPageError(head);
		for (i = PG_cont_ioredo_s; i <= PG_cont_ioredo_e; i++)
			clear_bit(i, &head->flags);
	}

	unlock_page(head);

	for (i = 1; i < HPAGE_CONT_PTE_NR; i++)
		clear_bit(PG_locked, &head[i].flags);
	put_page(head);
}

static LIST_HEAD(thp_queue);
static DEFINE_SPINLOCK(thp_queue_lock);

static void thp_queue_add(struct page *page)
{
	unsigned long flags;

	spin_lock_irqsave(&thp_queue_lock, flags);
	list_add_tail(&page->lru, &thp_queue);
	spin_unlock_irqrestore(&thp_queue_lock, flags);
}

static struct page *thp_queue_remove(void)
{
	unsigned long flags;
	struct page *page;

	spin_lock_irqsave(&thp_queue_lock, flags);
	page = list_first_entry_or_null(&thp_queue, struct page, lru);
	if (page)
		list_del(&page->lru);
	spin_unlock_irqrestore(&thp_queue_lock, flags);

	return page;
}

static void build_thp(struct work_struct *work)
{
	struct page *head;

	while ((head = thp_queue_remove()))
		__build_thp(head->mapping, head);
}
static DECLARE_WORK(thp_queue_work, build_thp);
static struct workqueue_struct *build_thp_wq;

#if defined(CONFIG_DEBUG_LOCK_ALLOC)
static DEFINE_SPINLOCK(cont_endio_lock);
#endif

void init_cont_endio_spinlock(struct inode *inode)
{
	/*
	 * with debug, spinlock will take 64bytes rather than 4 bytes
	 * (or 24 with DEBUG_SPINLOCK)
	 */
#if !defined(CONFIG_DEBUG_LOCK_ALLOC)
	spinlock_t *sp = (spinlock_t *)&inode->i_mapping->endio_spinlock;
	/* we are using android reserve2-4 */
	BUG_ON(sizeof(spinlock_t) > 3 * sizeof(unsigned long));
	spin_lock_init(sp);
#endif
}

void set_cont_pte_uptodate_and_unlock(struct page *page)
{
	struct address_space *mapping;
	bool page_uptodate  = true;
	bool page_error = false;
	unsigned long pfn;
	struct page *head;
	unsigned long flags;
	spinlock_t *sp;
	int i;

	pfn = page_to_pfn(page);
	head = (struct page *)pfn_to_page(ALIGN_DOWN(pfn, HPAGE_CONT_PTE_NR));
	BUG_ON(!PageCont(head) || !PageCont(page));

	mapping = page->mapping;

	/* TODO: figure out why this is happening */
	if (PageCompound(page)) {
		pr_err("@@@FIXME: %s endio on THP: cont:%d %d index:%lx %lx mapping:%lx %lx pfn:%lx within:%d compound:%d update:%d\n",
				__func__, PageCont(head), PageCont(page), head->index, page->index, (unsigned long)mapping, (unsigned long)
				head->mapping, pfn, within_cont_pte_cma(pfn), PageTransCompound(page), PageUptodate(head));
		return;
	}
	BUG_ON(!mapping || ((mapping != head->mapping) && !PageCompound(page)));
	SetPageContUptodate(page);

#if defined(CONFIG_DEBUG_LOCK_ALLOC)
	sp = &cont_endio_lock;
#else
	sp = (spinlock_t *)&head->mapping->endio_spinlock;
#endif
	spin_lock_irqsave(sp, flags);
	for (i = 0; i < HPAGE_CONT_PTE_NR; i++) {
		BUG_ON(!PageCont(&head[i]));
		if (!PageContUptodate(&head[i])) {
			page_uptodate = false;
			break;
		}
	}

	if (page_uptodate) {
		for (i = 0; i < HPAGE_CONT_PTE_NR; i++) {
			/* users can re-read once */
			bool error = TestClearPageError(&head[i]);

			ClearPageContUptodate(&head[i]);
			if (error)
				page_error = error;
		}
	}
	spin_unlock_irqrestore(sp, flags);

	if (!page_uptodate)
		return;

	if (page_error)
		SetPageError(head);

	if (in_interrupt() || page_error) {
		thp_queue_add(head);
		queue_work(build_thp_wq, &thp_queue_work);
	} else {
		__build_thp(head->mapping, head);
	}
}

struct cma *cont_pte_cma;
unsigned long cont_pte_cma_size;
unsigned long cont_pte_sup_mem;
bool cont_pte_sup_prjname;
/* true by default, false when cont_pte_hugepage=off in cmdline */
bool cont_pte_hugepage_enable = true;

#define CONT_PTE_CMA_SIZE (768 * SZ_1M)
#define CONT_PTE_SUP_MEM_SIZE (8ul * SZ_1G)

static inline bool is_cont_pte_cma_full(void)
{
	return global_node_page_state(NR_FILE_THPS) * HPAGE_CONT_PTE_SIZE >=
		(cont_pte_cma_size - (cont_pte_cma_size >> 5));
}

static int __init cmdline_parse_cont_pte_cma(char *p)
{
	cont_pte_cma_size = memparse(p, &p);
	return 0;
}
early_param("cont_pte_cma", cmdline_parse_cont_pte_cma);

static int __init cmdline_parse_cont_pte_sup_mem(char *p)
{
	cont_pte_sup_mem = memparse(p, &p);
	return 0;
}
early_param("cont_pte_sup_mem", cmdline_parse_cont_pte_sup_mem);

static int __init cmdline_parse_prjname(char *p)
{
	const char *prjs[] = {
		"21871", "21872", "22823", NULL,
	};
	int i = 0;

	for (i = 0; prjs[i] && p; i++) {
		if (!strcmp(p, prjs[i])) {
			pr_info("%s support\n", prjs[i]);
			cont_pte_sup_prjname = true;
			break;
		}
	}
	return 0;
}
early_param("oplusboot.prjname", cmdline_parse_prjname);

static int __init cmdline_parse_disable(char *p)
{
	int ret;

	ret = kstrtobool(p, &cont_pte_hugepage_enable);
	if (!ret && !cont_pte_hugepage_enable)
		pr_info("cont_pte_hugepage is disabled\n");
	return 0;
}
early_param("cont_pte_hugepage", cmdline_parse_disable);

inline bool cont_pte_huge_page_enabled(void)
{
	return static_branch_likely(&cont_pte_huge_page_enabled_key);
}

void __init cont_pte_cma_reserve(void)
{
	int res;

	/* default size */
	if (cont_pte_cma_size == 0)
		cont_pte_cma_size = CONT_PTE_CMA_SIZE;

	if (cont_pte_sup_mem == 0)
		cont_pte_sup_mem = CONT_PTE_SUP_MEM_SIZE;

	if (!cont_pte_sup_prjname || !cont_pte_hugepage_enable ||
	    memblock_phys_mem_size() - memblock_reserved_size() < cont_pte_sup_mem) {
		pr_info("device does not support cont_pte_huge_page\n");
		return;
	}

	res = cma_declare_contiguous(0, cont_pte_cma_size, 0, 0,
			HPAGE_CONT_PTE_ORDER, false, "cont_pte",
			&cont_pte_cma);
	if (unlikely(res)) {
		pr_warn("cont_pte_cma: reservation failed: err %d", res);
		return;
	}

	static_branch_enable(&cont_pte_huge_page_enabled_key);
	pr_info("cont_pte_cma: reserved %lu MiB\n", cont_pte_cma_size / SZ_1M);
}

static int __init huge_page_pool_init(void)
{
	struct huge_page_pool *pool = &cont_pte_huge_page_pool;
	struct sched_attr attr = { .sched_nice = 10 };
	const char *kworker_name = "kcont_hugepaged";
	struct cpumask cpu_mask = { CPU_BITS_NONE };
	int ret, i;

	if (!cont_pte_huge_page_enabled())
		return -ENOMEM;

	build_thp_wq = create_singlethread_workqueue("build_thp");
	if (!build_thp_wq) {
		pr_warn("failed to create build_thp workqueue\n");
		return -ENOMEM;
	}

	INIT_LIST_HEAD(&pool->item);
	pool->count = 0;
#ifdef CONFIG_CONT_PTE_HUGEPAGE_ON_QEMU
	/* on qemu, we have much less memory */
	pool->max = M2N(cont_pte_cma_size * 3 / 2);
	pool->high = M2N(SZ_4M);
#else
	pool->max = M2N(cont_pte_cma_size);
	pool->high = M2N(80 * SZ_1M);
#endif
	/* wakeup kthread on count < low, low = 3/4 high */
	pool->low = pool->high * 3 / 4;
	spin_lock_init(&pool->spinlock);
	pool->refill_worker = kthread_run(huge_page_pool_refill_worker, pool,
					  kworker_name);
	/* TDOO if failed */
	if (IS_ERR(pool->refill_worker)) {
		pr_err("failed to start %s\n", kworker_name);
		return 1;
	}

	ret = sched_setattr(pool->refill_worker, &attr);
	if (ret)
		pr_warn("failed to set priority for %s ret=%d\n",
			kworker_name, ret);

	/* TODO: move this to userspace, debug only */
	for (i = 0; i < 4; i++)
		cpumask_set_cpu(i, &cpu_mask);
	set_cpus_allowed_ptr(pool->refill_worker, &cpu_mask);

	pr_info("%s low: %d high:%d max: %d",
		__func__, pool->low, pool->high, pool->max);
	return ret;
}
core_initcall(huge_page_pool_init);

static int proc_stat_show(struct seq_file *s, void *v)
{
	int i = 0;
	struct huge_page_pool *pool = &cont_pte_huge_page_pool;

	seq_printf(s, "cont_pte_cma_size %lu\n", cont_pte_cma_size);
	seq_printf(s, "cont_pte_sup_mem %lu\n", cont_pte_sup_mem);
	seq_printf(s, "cont_cma_size %d\n", CONT_PTE_CMA_SIZE >> PAGE_SHIFT);
	seq_printf(s, "cont_page_flag 0x%lx\n",
		   1ul << PG_cont | 1ul << PG_cont_uptodate);

	seq_printf(s, "pool_low %d\n", pool->low * CONT_PTES);
	seq_printf(s, "pool_high %d\n", pool->high * CONT_PTES);
	seq_printf(s, "pool_cur %d\n", pool->count * CONT_PTES);


	seq_printf(s, "alloc %llu\n",
		   atomic64_read(perf_stat.alloc_retries + i));
	i++;

	for (; i <= MAX_POOL_ALLOC_RETRIES; i++)
		seq_printf(s, "alloc_%d %llu\n", i,
			   atomic64_read(perf_stat.alloc_retries + i));
	seq_printf(s, "alloc_fail %llu\n",
		   atomic64_read(perf_stat.alloc_retries + i));

	seq_printf(s, "direct_alloc: %llu\n",
		   atomic64_read(perf_stat.direct_alloc));
	seq_printf(s, "direct_alloc_slow: %llu\n",
		   atomic64_read(perf_stat.direct_alloc + 1));

	seq_printf(s, "direct_alloc_fail: %llu\n",
		   atomic64_read(perf_stat.direct_alloc_fail));
	seq_printf(s, "direct_alloc_fail_slow: %llu\n",
		   atomic64_read(perf_stat.direct_alloc_fail + 1));
	return 0;
}

#if CONFIG_CONT_PTE_HUGEPAGE_DEBUG
static int proc_fault_around_stat_show(struct seq_file *s, void *v)
{
	int i = 0;
	s64 counter, total = 0;

	seq_puts(s, "fault around stat:\n");
	for (; i < NR_FAULT_AROUND_STAT_ITEMS; i++) {
		counter = atomic64_read(&fault_around_stat[i]);
		total += counter;
		seq_printf(s, "fault-around[%d] %llu\n", i, counter);
	}
	seq_printf(s, "fault-around total %llu\n", total);

	return 0;
}
#endif

vm_fault_t cont_pte_filemap_around(struct vm_fault *vmf, pgoff_t start_pgoff, pgoff_t end_pgoff)
{
	struct vm_area_struct *vma = vmf->vma;
	struct file *file = vma->vm_file;
	struct address_space *mapping = file->f_mapping;
	struct page *page;
	vm_fault_t ret = 0;
	unsigned long addr = vmf->address;
	unsigned long haddr = addr & HPAGE_CONT_PTE_MASK;
	unsigned long end = min(vma->vm_end - 1, ALIGN_DOWN(haddr, SZ_2M) +  SZ_2M - 1);
	int hit, i;
	pgoff_t pgoff, last_pgoff, hoff;
	unsigned long around_cont = 0;

	hoff = ALIGN_DOWN(vmf->pgoff, HPAGE_CONT_PTE_NR);
	pgoff = last_pgoff = hoff;

	/*
	 * we are unable to map hugepage, but someone else might have read hugepage or
	 * basepages, map us as basepages from their pages(either hugepage or basepage)
	 */
	if (!transhuge_cont_pte_vma_suitable(vmf->vma, haddr)) {
		hit = find_get_cont_pte_pages(mapping, hoff, &page);
		/* try to map around base pages */
		if (hit != HIT_NOTHING) {
			if (page)
				put_page(page);
			if (hit != HIT_CONT)
				return vmf->vma->vm_ops->map_pages(vmf, start_pgoff, end_pgoff);
		}
		return 0;
	}

	if (pmd_none(*vmf->pmd)) {
		struct mm_struct *mm = vmf->vma->vm_mm;

		BUG_ON(pmd_trans_huge(*vmf->pmd));

		if (vmf->flags & FAULT_FLAG_SPECULATIVE)
			return VM_FAULT_RETRY;

		vmf->ptl = pmd_lock(mm, vmf->pmd);
		if (likely(pmd_none(*vmf->pmd))) {
			mm_inc_nr_ptes(mm);
			pmd_populate(mm, vmf->pmd, vmf->prealloc_pte);
			vmf->prealloc_pte = NULL;
		}
		spin_unlock(vmf->ptl);

		/* See comment in handle_pte_fault() */
		if (pmd_devmap_trans_unstable(vmf->pmd))
			return VM_FAULT_NOPAGE;
	}

	addr = haddr;
	if (!pte_map_lock_addr(vmf, addr)) {
		ret = VM_FAULT_RETRY;
		goto out;
	}

	for (i = 0; i < MAX_HUGEPAGE_MAPAROUND; i++) {
		int hit;
		unsigned long max_idx;

		if (haddr + (i + 1) * HPAGE_CONT_PTE_SIZE > end)
			break;

		pgoff = hoff + i * HPAGE_CONT_PTE_NR;
		hit = find_get_cont_pte_pages(mapping, pgoff, &page);
		if (hit == HIT_THP) {
			if (PageLocked(page))
				goto put;

			if (!PageUptodate(page) || PageReadahead(page))
				goto put;

			if (PageHWPoison(page))
				goto put;

			if (!trylock_page(page))
				goto put;

			if (page->mapping != mapping)
				goto unlock;

			if (!PageUptodate(page))
				goto unlock;

			max_idx = DIV_ROUND_UP(i_size_read(mapping->host), PAGE_SIZE);
			if (pgoff >= max_idx)
				goto unlock;

			addr += (pgoff - last_pgoff) << PAGE_SHIFT;
			vmf->pte += pgoff - last_pgoff;
			last_pgoff = pgoff;

			if (!cont_pte_none(vmf->pte))
				goto unlock;

			/* We're about to handle the fault */
			if (haddr == addr)
				ret = VM_FAULT_NOPAGE;

			do_set_cont_pte_with_addr(vmf, compound_head(page), addr);

			around_cont++;

			unlock_page(page);
			continue;
unlock:
			unlock_page(page);
put:
			put_page(page);
		} else {
			if (page)
				put_page(page);
		}
	}
	pte_unmap_unlock(vmf->pte, vmf->ptl);
out:

#if CONFIG_CONT_PTE_HUGEPAGE_DEBUG
	atomic_long_inc(&fault_around_stat[around_cont]);
#endif
	return ret;
}

static int __init proc_fs_pte_huge_page_init(void)
{
	struct proc_dir_entry *root_dir;

	if (!cont_pte_huge_page_enabled())
		return -ENOMEM;

	/* create base info */
	root_dir = proc_mkdir(KBUILD_MODNAME, NULL);

	if (!root_dir)
		return -ENOMEM;

	proc_create_single("stat", 0, root_dir, proc_stat_show);
#if CONFIG_CONT_PTE_HUGEPAGE_DEBUG
	proc_create_single("fault_around_stat", 0, root_dir, proc_fault_around_stat_show);
#endif
	return 0;
}
fs_initcall(proc_fs_pte_huge_page_init);
