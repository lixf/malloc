/* Xiaofan Li
 * xli2
 * 18213 f13
 * mallocLab 
 *
 *
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include "mm.h"
#include "memlib.h"
#include "contracts.h"
/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
# define dbg_heapCheck(...) mm_checkheap(__VA_ARGS__)
#else
# define dbg_printf(...)
# define dbg_heapCheck(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* my macros*/

#define WSIZE 8
#define DSIZE 16
#define MIN_BLK_SIZE 32 //header+footer+prev+next
#define TB_LEN 20 //table length = 20
#define SPL_TOR 4

#define CLASS3_MIN (1<<12)
#define CLASS3_MAX (1<<32)
#define CLASS2_MIN (1<< 6)
#define CLASS2_MAX (CLASS3_MIN-1)
#define CLASS1_MIN MIN_BLK_SIZE
#define CLASS1_MAX (CLASS2_MIN-1)


#define CHUNKSIZE (1<<12) //extend the heap by CHUNKSIZE
#define MAX(x,y) ((x)>(y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)      (*(long int *)(p))
#define PUT(p, val) (*(long int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - WSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* end my macros */

/* global variables */

static char* heap_listp;
static void** table;



/* function declarations*/

int mm_int(void);
static void* extend_heap(size_t words);

void* malloc(size_t size);
void free(void* ptr);
void* realloc(void* ptr,size_t size);
void* calloc(size_t nmemb,size_t size);
void mm_checkheap(int verbose);


char* split(void* block, size_t size,int index);
void tableAdd (char* bp);
static void* coalesce (char* bp);
int getIndex(size_t size);
static void place (char* bp, size_t size);
static char* find_fit(size_t size);
static int aligned(const void *p);


/*
 * inline helper for pointer arith
 * take out the block from the seglist table
 *
 */
inline void takeOut(long unsigned* ptr){ 
    
    //change the previous and next block in the table
    //*((char*)((*next)+WSIZE)) = *(next+WSIZE);
    long unsigned* prev_list = (long unsigned*) *ptr;
    long unsigned* next_list = (long unsigned*) *(ptr+1);
    long unsigned* prev_next = (long unsigned*) *(prev_list+1);
    long unsigned* next_prev = (long unsigned*) *next_list;
        
    /*
     * set the previous free block point to the next one 
     * also set the prev of the next to point to the previous
     */ 
    prev_next = next_list;
    next_prev = prev_list;

    return;

}




/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
 
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(24*WSIZE)) == (void *)-1)
      dbg_printf("init problem\n");
      return -1;
    
    /* the first 20 blocks are table entries NULL-ed*/
    table = (void**)heap_listp;
    int i;
    for (i=0;i<20;i++){
        table[i] = NULL;
    }

    PUT(heap_listp + (20*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (21*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (22*WSIZE), PACK(0, 1));      /* Epilogue header */
    //heap_listp points to prilogue after init
    heap_listp += (20*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    

    //add the free block into the table
    tableAdd(heap_listp+(3*WSIZE));//give the blk ptr
    return 0;
}

/* 
 * helper function for init
 * extends heap by words
 */
static void *extend_heap(size_t words) {
    char *bp;

    /* use mem_sbrk to allocate new heap */
    if ((long)(bp = mem_sbrk(words)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(words,0));      /* Free block header(previous epilogue)*/
    PUT(FTRP(bp), PACK(words,0));      /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));/* New epilogue*/

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * helper function for coalesce
 */

static void* coalesce (char* bp) {

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //case 1
    if (prev_alloc && next_alloc) {
        return bp;
    }
    
    //case 2
    else if (prev_alloc && !next_alloc) {
        //takes out the next blk after bp
        takeOut((long unsigned*)NEXT_BLKP(bp)); 

        //takes care of the physical adr stuff
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    //case 3
    else if (!prev_alloc && next_alloc) {
        //void* last_phy = PREV_BLKP(bp);
        //same as above
        //*(((char*)(*(char*)last))+WSIZE) = *((char*)last+WSIZE);
        //(*(*((char*)last+WSIZE))) = *last;

        takeOut((long unsigned*)PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    //case 4
    else {
        
        /*void* next = NEXT_BLKP(bp);
        void* last = PREV_BLKP(bp);
        
        *(((char*)(*(char*)next))+WSIZE) = *((char*)next+WSIZE);
        (*(*((char*)next+WSIZE))) = *next;
        *(((char*)(*(char*)last))+WSIZE) = *((char*)last+WSIZE);
        (*(*((char*)last+WSIZE))) = *last;
        */
        takeOut((long unsigned*)PREV_BLKP(bp));
        takeOut((long unsigned*)NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    //re-add coalesced bp
    tableAdd(bp);
    mm_checkheap(1);

    return bp;

}
/* 
 * Uses the 20 blocks as a lookup table, covering different size of requests
 * Class 1: index 0 - 3; size 32B - 56B
 * Class 2: index 4 - 9; size 1<<6 - 1<<12 -1
 * Class 3: index 10-19; size 1<<12 - 1<<32
 *
 */
int getIndex(size_t size){
    
    int index = -1;
    //check for class
    /*if (size > CLASS3_MAX){
        dbg_printf("block too big!\n");
        exit(1);
    } */
    if (size > CLASS3_MIN){
        //in class 3 get highest bit
        int i;
        for(i=32;i>11;i--){
            int map = 1<<i;
            if ((size&map)==1){
              index = ((i -12)/2)+10;
              break;
            }
        }
    }
    else if (size > CLASS2_MIN){
        //in class 2 get highest bit
        int i;
        for(i=11;i>5;i--){
            int map = 1<<i;
            if((size&map)==1){
              index = i-2;//i-6+4
              break;
            }
        }
    }
    else{
        //in class 3
        index = (size -32)/8; 
    }

    return index;
}
/* 
 * adds a free block to the seg list table
 * used when: extending heap, coalescing
 */

void tableAdd (char* bp){
    
    int size = GET_SIZE(HDRP(bp));
    ASSERT(size>MIN_BLK_SIZE);
    ASSERT(GET_ALLOC((HDRP(bp))==0));
    int index;

    index = getIndex(size);
    ASSERT (index>=0 && index<20);

    //change the table[index]maybe TODO
    void* next = table[index];
    table[index] = bp;
    *(long unsigned*)bp = (long unsigned)NULL;
    *(long unsigned*)(bp + WSIZE) = (long unsigned)next;
    *(long unsigned*)next = (long unsigned)bp;
    return;
}


/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;


    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. 
     * changed to WSIZE = 8 Bytes
     * asize describes the payload + hearder + footer
     */
    if (size <= WSIZE)
        asize = WSIZE+2*WSIZE;
    else
        asize = WSIZE * (2+(size + (WSIZE) + (WSIZE-1)) / WSIZE);


    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}


/*
 * helper function for malloc: place 
 */

void place (char* bp, size_t size) {
  //size is aligned to 8B in malloc
  int blkSize = GET_SIZE(HDRP(bp));
  ASSERT(blkSize>=size);
  
  int index = getIndex(blkSize);
  //take out the blk
  takeOut((long unsigned*) bp);
  
  bp = split(bp,size,index);

  PUT(HDRP(bp),PACK(blkSize,1));
  PUT(FTRP(bp),PACK(blkSize,1));
  dbg_heapCheck(1);
  return;
} 

/*
 * helper function for malloc : find_fit
 */

static char* find_fit (size_t size){
    int index;
    index = getIndex(size);
    if (index==-1) return NULL;
    
    ASSERT(index>=0 && index<20);
    
    //take out the first one
    char* temp = table[index];
    while(temp != NULL){
        if ((size_t)GET_SIZE(HDRP(temp))>=size)
            return temp;
        temp = (char*)(*(long unsigned*)(temp+WSIZE));
    }
    //only returns a ptr to the right blk
    //doesn't change ptr around nor split

    return NULL;
    
    //char* next = *(temp+WSIZE);
    //table[index] = next;
    //*next = NULL;
}

char* split(void* block, size_t size,int index){
    //don't bother spliting if in class 1
    if (index<4) return (char*)block;
    
    int diff = GET_SIZE(HDRP((char*)block)) - size;
    //SPL_TOR = split tolerance default = 4
    //the higher it is, more utilization less efficiency
    if (diff < (size/SPL_TOR)) return (char*)block;
    else {
        //splits into two aligned blocks
        ASSERT(diff>MIN_BLK_SIZE);
        PUT(HDRP(block),PACK(size+2*WSIZE,0));
        PUT(FTRP(block),PACK(size+2*WSIZE,0));
        PUT(HDRP(NEXT_BLKP(block)),PACK(diff-2*WSIZE,0));
        PUT(FTRP(NEXT_BLKP(block)),PACK(diff-2*WSIZE,0));
        
        tableAdd(NEXT_BLKP(block));
        
        dbg_heapCheck(1);
        return (char*)block;
    }
}



/*
 * free
 */
void free (void* ptr) {
    if (!ptr) return;

    char* bp = ptr;
    size_t size = GET_SIZE(HDRP(bp));
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    coalesce(bp);
    dbg_heapCheck(1);
    return;
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    return NULL;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    return NULL;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/* helper for the heap checker
 * returns num of free lists 
 * returns -1 on error
 */
static int valid_list(void* bucket,int index){
    //count number of free lists
    int count = 0;
    char* bp = bucket;
    if (bp==NULL) return 0; //if nothing is in the list
    
    char* next = *(bp + WSIZE);

    //check if the size is in the right bucket
    while (bp != NULL) {
        count++;
        int size = GET_SIZE(HDRP(bp)); 
        if(!(getIndex(size)==index)){
            dbg_printf("wrong bucket\n");
            return -1;
        }
        bp = next;
        next = *(bp+WSIZE);
    }
    return count;
}
/* helper for heap checker 
 * returns num of free lists in total
 * returns -1 on error
 */

static int valid_table(void){
    int countTB;
    int countList;
    
    if (table == NULL) 
        dbg_printf("table init prob\n");
        return -1;
    int i;
    for(i = 0;i<tb_len;i++){
        if((countList = valid_list(table[i],i))==-1){
            dbg_printf("list prob\n");
            return -1;
        }
        else {
            countTB += countList;
        }
    }
    return countTB;
}


/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
    //always verbose
    verbose = 1;
    
    //counting free lists
    int intern_count=0;
    int out_count=0;
    char* current = heap_listp;
    char* next = current + 3*WSIZE;
    int preAlloc = -1; //invalid at beginning checks if coalescing is good

    if (current==NULL || next==NULL) 
        dbg_printf("starting pointers NULL\n");
        exit(1);

    if (current != ((char*)table+20*WSIZE))
        dbg_printf("table length problem\n");
        exit(1);

    //check prologue
    if(GET_SIZE(current)!=16 || GET_SIZE(current+WSIZE)!=16
        || GET_ALLOC(current)!=1 || GET_ALLOC(current+WSIZE)!=1)
        dbg_printf("prologue wrong\n");
        exit(1);


    //check everything else in the middle
    while(GET_SIZE(next) != 0){ //epilogue
        
        current = next;
        next = NEXT_BLKP(current);
        intern_count++;


        //1.checks footer header consistency
        int sizeH = GET_SIZE(HDRP(current));
        int sizeF = GET_SIZE(FTRP(current));
        int allocH = GET_ALLOC(HDRP(current));
        int allocF = GET_ALLOC(FTRP(current));
        if (sizeH != sizeF || allocH != allocF)
            dbg_printf("H-F problem\n");
            exit(1);

        //2.checks alignment
        if (!aligned((void*)current))
            dbg_printf("alignment problem\n");
            exit(1);

        //3.checks heap boundaries
        if (!in_heap((void*)current))
            dbg_printf("outside heap\n")
            exit(1);
            
        //4.checks coalescing
        if (preAlloc == allocH)
            dbg_printf("coalescing problem\n");
            exit(1);
        
    }
    
    
    //check the seg list
    if ((out_count = valid_table())==-1){
        dbg_printf("table problem\n");
        exit(1);    
      }
    else {
        if (out_count != intern_count) 
            dbg_printf("num of free lists not same\n");
            exit(1);  
      }

    return;
}
