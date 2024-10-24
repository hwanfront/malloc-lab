/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define WSIZE 8
#define DSIZE 16
#define CHUNKLEN 6
#define CHUNKSIZE (1<<CHUNKLEN)
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*(char **)(bp + WSIZE))

static char *heap_listp;
static char *free_listp[CHUNKLEN + 1];
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *best_fit(size_t asize);
static void place(void *bp, size_t asize);

static void connect(void *bp);
static void disconnect(void *bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // create init empty heap
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
        return -1;
    // Alignment padding
    
    PUT(heap_listp, 0);
    // Prologue header
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1)); 
    // predecessor, successor
    PUT(heap_listp + (2 * WSIZE), (unsigned int)NULL);
    PUT(heap_listp + (3 * WSIZE), (unsigned int)NULL);
    // Prologue footer
    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1)); 
    // epilogue header
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1)); 
    // 힙 시작 위치
    int i;
    for(i = 0; i < CHUNKLEN + 1; i++) {
        free_listp[i] = heap_listp + (2 * WSIZE);
    }
    heap_listp += (2 * WSIZE);

    // extend the empty heap with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((bp = mem_sbrk(size)) == (void*)-1)
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size <= 0) 
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (size <= 0) { 
        mm_free(ptr);
        return NULL;
    }

    if (ptr == NULL) {
        return mm_malloc(size); 
    }

    size_t old_size = GET_SIZE(HDRP(ptr));
    size_t new_size = ALIGN(size + DSIZE);

    // 요청된 크기가 기존 블록보다 크기가 작거나 같다면 기존 블록 사용
    if (new_size <= old_size) {
        return ptr;
    }

    // 다음 블록 free, 병합해서 크기가 충분하면
    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) && (old_size + GET_SIZE(HDRP(NEXT_BLKP(ptr))) >= new_size)) {
        size_t combined_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        disconnect(NEXT_BLKP(ptr));  // 가용 리스트에서 다음 블록을 제거
        PUT(HDRP(ptr), PACK(combined_size, 1));
        PUT(FTRP(ptr), PACK(combined_size, 1));
        return ptr;
    }

    void *newptr = mm_malloc(size);
    if (newptr == NULL) {
        return NULL;
    }

    memcpy(newptr, ptr, old_size - DSIZE);
    mm_free(ptr);

    return newptr;
}

static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case 1
    if(prev_alloc && next_alloc) {
        connect(bp);
        return bp;
    }

    // case 2
    else if (prev_alloc && !next_alloc) {
        disconnect(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3
    else if (!prev_alloc && next_alloc) {
        disconnect(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }

    // case 4
    else {
        disconnect(PREV_BLKP(bp));
        disconnect(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    connect(bp);
    return bp;
}

static int get_list_index(size_t size) {
    int index = 0;
    while (index < CHUNKLEN && size > 1) {
        size >>= 1;
        index++;
    }
    return index;
}

static void *first_fit(size_t asize) {
    void *bp = free_listp[get_list_index(asize)];
    while (GET_ALLOC(HDRP(bp)) != 1) {
        if(GET_SIZE(HDRP(bp)) >= asize){
            return bp;
        }
        bp = SUCC(bp);
    }
    return NULL;
}

static void *best_fit(size_t asize) {
    void *bp = free_listp[get_list_index(asize)];
    void *min_size_bp = NULL;
    size_t min_size = (size_t) - 1;

    while (GET_ALLOC(HDRP(bp)) != 1) {
        if (GET_SIZE(HDRP(bp)) == asize) {
            return bp;
        }
        if (GET_SIZE(HDRP(bp)) > asize && GET_SIZE(HDRP(bp)) < min_size) {
            min_size = GET_SIZE(HDRP(bp));
            min_size_bp = bp;
        }
        bp = SUCC(bp);
    }
    
    return min_size_bp;
}

static void *find_fit(size_t asize) {
    return best_fit(asize);
    // return first_fit(asize);
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    
    disconnect(bp);
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        connect(bp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void connect(void *bp) {
    int idx = get_list_index(GET_SIZE(HDRP(bp)));
    SUCC(bp) = free_listp[idx];
    PRED(bp) = NULL;
    PRED(free_listp[idx]) = bp;
    free_listp[idx] = bp;
}

static void disconnect(void *bp) {
    int idx = get_list_index(GET_SIZE(HDRP(bp)));
    if(bp == free_listp[idx]) {
        PRED(SUCC(bp)) = NULL;
        free_listp[idx] = SUCC(bp);
        return;
    } 
    SUCC(PRED(bp)) = SUCC(bp);
    PRED(SUCC(bp)) = PRED(bp);
}
