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
# define dbg_printf(...) {printf(__VA_ARGS__); printf("*****in %s*****\n",__func__);}
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

#define CLASS1_MIN (1<<12)
#define CLASS1_MAX (1<<31)
#define CLASS2_MIN (1<< 6)
#define CLASS2_MAX (CLASS3_MIN-1)
#define CLASS3_MIN MIN_BLK_SIZE
#define CLASS3_MAX (CLASS2_MIN-1)


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
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* end my macros */

/* global variables */

static char* heap_listp;
static void** table;
static char* heap_max;


/* function declarations*/

int mm_init(void);
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
void takeOut(long unsigned* ptr){ 
    //change the previous and next block in the table
    assert(ptr !=NULL);
    long unsigned* prev_list = (long unsigned*) *ptr;
    long unsigned* next_list = (long unsigned*) *(ptr+1);
    long unsigned* prev_next = NULL;
    long unsigned* next_prev = NULL;
    
    printf("ptr %p pl %p, nl %p\n",ptr,prev_list,next_list);
    if(prev_list != NULL && next_list == NULL){

            prev_next = (long unsigned*) (*(prev_list+1));
            
            prev_next = NULL;
            prev_list = NULL;
            printf("pn %p\n",prev_next);
            return;
        } 
    else if (prev_list == NULL && next_list == NULL){
            
            //list had only one elem
            table[getIndex(GET_SIZE(HDRP(ptr)))] = NULL;
            return;
        }
    else if(prev_list == NULL && next_list != NULL){
            
            //the first one in the list
            char* bp = (char*) ptr;
            printf("next_list%p,bp%p\n",next_list,bp);
            table[getIndex(GET_SIZE(HDRP(bp)))] = next_list;
            next_prev = (long unsigned*) *next_list;
            
            printf("next_prev%p\n",next_prev);
            next_prev = NULL;
            next_list = NULL;
            printf("next_prev%p nextlist%p\n",next_prev,next_list);
            return;
        }
    else{
      //if(prev_list != NULL && next_list != NULL){
            prev_next = (long unsigned*) *(prev_list+1);
            next_prev = (long unsigned*) *next_list; 
            prev_next = next_list;
            next_prev = prev_list;
            return;
        }
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(23*WSIZE)) == (void *)-1){
      dbg_printf("init problem\n");
      return -1;
    }
   
    /* the first 20 blocks are table entries NULL-ed*/
    table = (void**)heap_listp;
    int i;
    for (i=0;i<20;i++){
        table[i] = NULL;
    }

    
    heap_listp += (20*WSIZE);
    heap_max = heap_listp + (unsigned)CLASS1_MAX;

    PUT(heap_listp , PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (2*WSIZE), PACK(0, 1));      /* Epilogue header */
    //heap_listp points to prilogue after init

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
     
    return 0;
}

/* 
 * helper function for init
 * extends heap by words
 */
static void *extend_heap(size_t words) {
    char *bp;

    if((long unsigned)mem_heap_hi()+words > (long unsigned)heap_max) return NULL; 
    /* use mem_sbrk to allocate new heap */
    if ((long)(bp = mem_sbrk(words)) == -1)
        return NULL;
    dbg_printf("new bp:%p,heap_max:%p,heap_listp:%p\n",bp,heap_max,heap_listp);    
   

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(words,0));      /* Free block header(previous epilogue)*/
    PUT(FTRP(bp), PACK(words,0));      /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));/* New epilogue*/
    dbg_printf("bp:%p,hd:%p,ft:%p,ep:%p\n",bp,HDRP(bp),FTRP(bp),NEXT_BLKP(bp));
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * helper function for coalesce
 */

static void* coalesce (char* bp) {

    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    dbg_printf("prev_alloc:%d,next_alloc:%d,next_size:%d,size:%d\n",(int)prev_alloc,(int)next_alloc,(int)next_size,(int)size);
    //case 1
    if (prev_alloc && next_alloc) {
        dbg_printf("checking heap\n"); 
        tableAdd(bp);
        dbg_heapCheck(1);
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
    dbg_printf("before check\n");
    dbg_heapCheck(1);
    dbg_printf("passed check in coal\n");
    return bp;

}
/* 
 * Uses the 20 blocks as a lookup table, covering different size of requests
 * Class 3: index 0 - 3; size 32B - 56B
 * Class 2: index 4 - 9; size 1<<6 - 1<<12 -1
 * Class 1: index 10-19; size 1<<12 - 1<<32
 *
 */
int getIndex(size_t size){
    int index = -1;
    dbg_printf("size to look up: %d\n",(int)size);
    //check for class
    if ((long unsigned)size > (long unsigned)CLASS1_MAX){
        dbg_printf("block too big!\n");
        return index;
    } 
    if (size >= CLASS1_MIN){
        //in class 1 get highest bit
        dbg_printf("in class 1\n");
        int i;
        for(i=32;i>11;i--){
            int map = 1<<i;
            if ((size&map)!=0){
              index = ((i -12)/2)+10;
              break;
            }
        }
    }
    else if (size >= CLASS2_MIN){
        //in class 2 get highest bit        
        dbg_printf("in class 2\n");
        int i;
        for(i=11;i>5;i--){
            int map = 1<<i;
            //printf("size:%d,map:%d,&:%d\n",(int)size,map,(int)(map&size));
            if((size&map)!=0){
              index = i-2;//i-6+4
              break;
            }
        }
    }
    else{
        //in class 3
        dbg_printf("in class 3\n");
        index = (size -32)/8; 
    }
    ASSERT(index >= 0 && index < 20);
    return index;
}
/* 
 * adds a free block to the seg list table
 * used when: extending heap, coalescing
 */

void tableAdd (char* bp){
    
    int size = GET_SIZE(HDRP(bp));

    assert(size>MIN_BLK_SIZE);
    assert(GET_ALLOC(HDRP(bp))==0);
    int index;

    index = getIndex(size);
    dbg_printf("index to add to %d,bp:%p\n",index,bp);
    if (index ==-1) 
      return;

    //change the table[index]maybe TODO
    long unsigned* next = (long unsigned*)table[index];
    table[index] = (void*)bp;
    *(long unsigned*)bp = 0;
    *((long unsigned*)(bp + WSIZE)) = (long unsigned)next;
    if (next !=NULL) *next = (long unsigned)bp;
    dbg_printf("hi from add to table %p,next%p\n",table[index],next);
    return;
}


/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    dbg_printf("requesting size: %d\n",(int)size);
    /* Ignore spurious requests */
    if (size == 0 || size >= (long unsigned)CLASS1_MAX)
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
    dbg_printf("going to extend for size:%d\n",(int)asize);
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}


/*
 * helper function for malloc: place 
 */

void place (char* bp, size_t size) {
  //size is aligned to 8B in malloc
  unsigned blkSize = GET_SIZE(HDRP(bp));

  assert(blkSize>=size);
  dbg_printf("before takeOut: prev blk, hd:%d,ft:%d\n",(int)GET_SIZE(HDRP(PREV_BLKP(bp))),(int)GET_SIZE(FTRP(PREV_BLKP(bp))));
  int index = getIndex(blkSize);
  //take out the blk
  takeOut((long unsigned*) bp);
  dbg_printf("after takeOut: prev blk, hd:%d,ft:%d\n",(int)GET_SIZE(HDRP(PREV_BLKP(bp))),(int)GET_SIZE(FTRP(PREV_BLKP(bp)))); 
  bp = split(bp,size,index);

  size = GET_SIZE(HDRP(bp));
  PUT(HDRP(bp),PACK(size,1));
  PUT(FTRP(bp),PACK(size,1));
  dbg_printf("bpuft:%p,prevft:%p\n",FTRP(bp),FTRP(PREV_BLKP(bp)));
  dbg_printf("just placed: hd:%d,ft:%d\n",(int)GET_SIZE(HDRP(bp)),(int)GET_SIZE(HDRP(bp)));
  dbg_printf("prev blk, hd:%d,ft:%d\n",(int)GET_SIZE(HDRP(PREV_BLKP(bp))),(int)GET_SIZE(FTRP(PREV_BLKP(bp)))); 
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
    
    assert(index>=0 && index<20);
    
    //take out the first one
    char* temp = table[index];
    while(temp != NULL){
        dbg_printf("in look up, blk_size is%d,size is%d\n",(int)GET_SIZE(HDRP(temp)),(int)size);
        if ((size_t)GET_SIZE(HDRP(temp))>=size){
            return temp;
        }
        temp = (char*)(*(long unsigned*)(temp+1));
    }
    //only returns a ptr to the right blk
    //doesn't change ptr around nor split

    return NULL;
    
    //char* next = *(temp+WSIZE);
    //table[index] = next;
    //*next = NULL;
}
/*
 * takes in a ptr to a payload 
 * split the block if too big 
 * add the split block back to table
 */
char* split(void* block, size_t size,int index){
    //don't bother spliting if in class 1
    if (index<4) return (char*)block;
    //assert((size_t)GET_SIZE(HDRP(block))>=size); 
    int diff = GET_SIZE(HDRP((char*)block)) - size;
    
    dbg_printf("diff is %d, blk_size is%d,size is%d\n",diff,(int)GET_SIZE(HDRP(block)),(int)size);


    //SPL_TOR = split tolerance default = 4
    //the higher it is, more utilization less efficiency
    if ((unsigned)diff < (size/SPL_TOR)) {
      return (char*)block;
    }
    else {
        //splits into two aligned blocks
        assert(diff>MIN_BLK_SIZE);
        PUT(HDRP(block),PACK(size,0));
        PUT(FTRP(block),PACK(size,0));
        dbg_printf("new blk: hd:%d,ft:%d\n",(int)GET_SIZE(HDRP(block)),(int)GET_SIZE(FTRP(block)));
        PUT(HDRP(NEXT_BLKP(block)),PACK(diff,0));
        PUT(FTRP(NEXT_BLKP(block)),PACK(diff,0));
        
        tableAdd(NEXT_BLKP(block));
        printf("new blk added size:%d\n",(int)GET_SIZE(HDRP(NEXT_BLKP(block))));
        
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
    oldptr = oldptr;
    size=size;
    return NULL;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    nmemb = nmemb;
    size = size;
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
    //count number of free blks
    int count = 0;
    long unsigned* bp = bucket;
    if (bp==NULL) return 0; //if nothing is in the list
    
    long unsigned* next = (long unsigned*)(*(bp + 1));

    //check if the size is in the right bucket
    while (bp != NULL) {
        count++;
        printf("index: %d bp:%p next %p\n",index,bp,next);
        next = (long unsigned*)(*(bp + 1));
        int size = GET_SIZE(HDRP(bp)); 
        if(!(getIndex(size)==index)){
            dbg_printf("wrong bucket,size:%d;index:%d,should be:%d,bp:%p\n",size,index,getIndex(size),bp);
            return -1;
        }
        bp = next;

    }
    return count;
}
/* helper for heap checker 
 * returns num of free lists in total
 * returns -1 on error
 */

static int valid_table(void){
    int countTB = 0;
    int countList = 0;
    
    if (table == NULL){ 
        dbg_printf("table init prob\n"); 
        return -1;
    }
    int i;
    for(i = 0;i<20;i++){
        if((countList = valid_list(table[i],i))==-1){
            dbg_printf("list prob:%d\n",i);
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
    int intern_count;
    int out_count;
    intern_count = 0;
    out_count=0;
    char* current = heap_listp;
    char* next = current + 3*WSIZE;
    int preAlloc = -1; //invalid at beginning checks if coalescing is good

    if (current==NULL){ 
        dbg_printf("starting pointers NULL\n");
        exit(1);
    }

    if (current != ((char*)table+20*WSIZE)){
        dbg_printf("table length problem\n");
        exit(1);
    }
    
    //check prologue
    if(GET_SIZE(current)!=16 || GET_SIZE(current+WSIZE)!=16
        || GET_ALLOC(current)!=1 || GET_ALLOC(current+WSIZE)!=1){
        dbg_printf("prologue wrong,%ld,%ld,%ld,%ld\n",GET_SIZE(current),GET_SIZE(current+WSIZE),GET_ALLOC(current),GET_ALLOC(current+WSIZE));
        exit(1);
    }

    //check everything else in the middle
    while(!(GET_SIZE(HDRP(next)) == 0 && GET_ALLOC(HDRP(next))==1)){ //epilogue
        
        current = next;
        next = NEXT_BLKP(current);
        if (GET_ALLOC(HDRP(current))==0) intern_count++;


        //1.checks footer header consistency
        int sizeH = GET_SIZE(HDRP(current));
        int sizeF = GET_SIZE(FTRP(current));
        int allocH = GET_ALLOC(HDRP(current));
        int allocF = GET_ALLOC(FTRP(current));
        dbg_printf("%d,%d,%d,%d\n",sizeH,sizeF,allocH,allocF);
        if (sizeH != sizeF || allocH != allocF){
            dbg_printf("H-F problem\n");
            exit(1);
        }

        //2.checks alignment
        if (!aligned((void*)current)){
            dbg_printf("alignment problem\n");
            exit(1);
        }

        //3.checks heap boundaries
        if (!in_heap((void*)current)){
            dbg_printf("outside heap\n");
            exit(1);
        }
            
        //4.checks coalescing
        if (preAlloc == allocH){
            dbg_printf("coalescing problem\n");
            exit(1);
        }
    }
    
    dbg_printf("checking seg list,out_count %d\n",out_count);   
    //check the seg list
    if ((out_count = valid_table())==-1){
        dbg_printf("table problem %d\n",out_count);
        exit(1);
    }else if (out_count != intern_count) {
            dbg_printf("num of free lists not same,in %d;out %d\n",intern_count,out_count);
            exit(1);  
      }

    return;
}
