#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "ateam",
    "junghwan",
    "kim015jh@gmail.com",
    "",
    ""
};

// 리스트 조작을 위한 기본 상수 등 매크로

#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// word, double word 크기
#define WSIZE 8
#define DSIZE 16

// heap 이 커질 때 확장되는 최소 크기
#define CHUNKSIZE (1<<7)
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 블록의 사이즈 (
#define GET_SIZE(p) (GET(p) & ~0x7)

// 블록의 allocated 필드 (0 이면 free, 1 이면 allocated 상태를 의미)
#define GET_ALLOC(p) (GET(p) & 0x1)

// header 포인터는 bp 주소 - word size
#define HDRP(bp) ((char *)(bp) - WSIZE)

// footer 포인터는 bp 주소 + 블록 사이즈(헤더와 GET_SIZE 를 통해 읽어옴) - double word size
// 예시) 블록 사이즈가 16, w 사이즈가 4일 때
// │16/1│    │    │16/1│    │ ...
//      └ bp 
// │16/1│    │    │16/1│    │ ...
//                          └ bp + 12
//                            (char *)(bp) + GET_SIZE(HDRP(bp))
// │16/1│    │    │16/1│    │ ...
//                └ bp + 12 - 8
//                  (char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음 블록포인터 위치
// 예시) 블록 사이즈가 16, w 사이즈가 4일 때
// │16/1│    │    │16/1│ss/m│ ...
// │    └ bp 
// └ bp - WSIZE
//   GET_SIZE((char *)(bp) - WSIZE) == 12

// │16/1│    │    │16/1│ss/m│ ...
//                          └ bp + 12
//                            (char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))

// 이전 블록포인터 위치
// 예시) 블록 사이즈가 12, w 사이즈가 4일 때
// │16/1│    │    │16/1│12/1│    │12/1│
//                │         └ bp 
//                └ bp - DSIZE
//                  GET_SIZE((char *)(bp) - DSIZE) == 16

// │16/1│    │    │16/1│12/1│    │12/1│
//      └ bp - 16
//        (char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*(char **)(bp + WSIZE))

static char *free_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static void connect(void *bp);
static void disconnect(void *bp);

int mm_init(void)
{
    if ((free_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
        return -1;
    PUT(free_listp, 0);
    PUT(free_listp + (1 * WSIZE), PACK(2 * DSIZE, 1)); 
    // predecessor, successor
    PUT(free_listp + (2 * WSIZE), (unsigned int)NULL);
    PUT(free_listp + (3 * WSIZE), (unsigned int)NULL);
    PUT(free_listp + (4 * WSIZE), PACK(2 * DSIZE, 1)); 
    PUT(free_listp + (5 * WSIZE), PACK(0, 1)); 
    free_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) 
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

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

void *mm_realloc(void *ptr, size_t size) {
    if (size <= 0) { 
        mm_free(ptr);
        return NULL;
    }

    if (ptr == NULL) {
        return mm_malloc(size); 
    }

    size_t old_size = GET_SIZE(HDRP(ptr));
    size_t new_size = ALIGN(size + DSIZE);

    if (new_size <= old_size) {
        return ptr;
    }


    void *next_bp = HDRP(NEXT_BLKP(ptr));
    if (!GET_ALLOC(next_bp) && (old_size + GET_SIZE(next_bp) >= new_size)) {
        size_t combined_size = old_size + GET_SIZE(next_bp);
        disconnect(NEXT_BLKP(ptr));
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

static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case 1
    if(prev_alloc && next_alloc) {
        connect(bp); // @
        return bp;
    }

    // case 2
    else if (prev_alloc && !next_alloc) {
        disconnect(NEXT_BLKP(bp)); // @
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3
    else if (!prev_alloc && next_alloc) {
        disconnect(PREV_BLKP(bp)); // @
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }

    // case 4
    else {
        disconnect(PREV_BLKP(bp)); // @
        disconnect(NEXT_BLKP(bp)); // @
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    connect(bp); // @
    return bp;
}


// static void *first_fit(size_t asize) {
//     void *bp;
    
//     for(bp = free_listp; GET_SIZE(HDRP(bp)); bp = NEXT_BLKP(bp)) {
//         if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
//             return bp;
//         }
//     }
//     return NULL;
// }

static void *best_fit(size_t asize) {
    void *bp = free_listp;
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
    
    disconnect(bp); // @
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        connect(bp); // @
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

// PREDECESSOR, SUCCESSOR 포인터 연결
static void connect(void *bp) {
    SUCC(bp) = free_listp;
    PRED(bp) = NULL;
    PRED(free_listp) = bp; 
    free_listp = bp;
}

// PREDECESSOR, SUCCESSOR 포인터 연결 해제
static void disconnect(void *bp) {
    if(bp == free_listp) {
        PRED(SUCC(bp)) = NULL;
        free_listp = SUCC(bp);
        return;
    } 
    SUCC(PRED(bp)) = SUCC(bp);
    PRED(SUCC(bp)) = PRED(bp);
}