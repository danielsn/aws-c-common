#include<stdlib.h>

#define MAX_INITIAL_ITEM_ALLOCATION 2
#define MAX_ITEM_SIZE 15
#define MAX_STR_LEN 32
#define MAX_BUF_LEN 32

#define ASSUME_VALID_MEMORY(ptr) ptr = malloc(sizeof(*(ptr)))
#define ASSUME_VALID_MEMORY_COUNT(ptr, count) ptr = malloc(sizeof(*(ptr)) * (count))
#define ASSUME_DEFAULT_ALLOCATOR(allocator) allocator = aws_default_allocator()
#define ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size) list = get_arbitrary_array_list( (item_count), (item_size) )

int nondet_int();
size_t nondet_size_t();
void *nondet_void_ptr();

struct aws_array_list *get_arbitrary_array_list(size_t item_count, size_t item_size) {
    struct aws_array_list *list;

    /* Assume list is allocated */
    ASSUME_VALID_MEMORY(list);

    /**
    * We should use here aws_mul_size_checked(item_count, item_size, &allocation_size)
    */
    size_t allocation_size = item_count * item_size;
    list->current_size = allocation_size;
    list->item_size = item_size;
    list->length = item_count;
    __CPROVER_assume(list->length >=0 && list->length <= item_count);

    if (nondet_int()) { /* Dynamic initialization */
        /* Use default allocator */
        struct aws_allocator *allocator = malloc(sizeof(*allocator));
        ASSUME_DEFAULT_ALLOCATOR(allocator);
        list->alloc = allocator;

        /**
        * Since we want an allocation that can never fail, use straight malloc here
        * allocation_size > 0 ? malloc(allocation_size) : NULL;
        */
        list->data = malloc(allocation_size);
    } else { /* Static initialization */
        list->alloc = NULL;

        /**
        * Since we want an allocation that can never fail, use straight malloc here
        * allocation_size > 0 ? malloc(allocation_size) : NULL;
        */
        void *raw_array = malloc(allocation_size);
        list->data = raw_array;
    }

    return list;
}
