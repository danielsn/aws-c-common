/*
 * Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <proof_helpers/make_common_data_structures.h>

struct aws_array_list *make_arbitrary_array_list(size_t initial_item_allocation, size_t item_size) {
    __CPROVER_assume(item_size != 0);
    struct aws_array_list *list;

    /* Assume list is allocated */
    ASSUME_VALID_MEMORY(list);

    if (nondet_int()) { /* dynamic */
        struct aws_allocator *allocator = malloc(sizeof(*allocator));
        ASSUME_CAN_FAIL_ALLOCATOR(allocator);
        list->alloc = allocator;
        size_t allocation_size;
        __CPROVER_assume(!aws_mul_size_checked(initial_item_allocation, item_size, &allocation_size));
        list->data = NULL;
        list->item_size = item_size;
        list->current_size = 0;
        list->length = 0;
        if (allocation_size > 0) {
            list->data = aws_mem_acquire(list->alloc, allocation_size);
            __CPROVER_assume(list->data != NULL);
            list->current_size = allocation_size;
        }
        __CPROVER_assume(list->current_size == 0 || list->data);
    } else { /* static */
        size_t len;
        __CPROVER_assume(!aws_mul_size_checked(initial_item_allocation, item_size, &len));
        void *raw_array = can_fail_malloc(len);
        __CPROVER_assume(raw_array != NULL);
        __CPROVER_assume(initial_item_allocation != 0);
        list->alloc = NULL;
        __CPROVER_assume(!aws_mul_size_checked(initial_item_allocation, item_size, &list->current_size));
        list->item_size = item_size;
        list->length = 0;
        list->data = raw_array;
    }
    list->length = nondet_size_t();
    __CPROVER_assume(list->length <= initial_item_allocation);
    return list;
}

struct aws_array_list *make_nondet_array_list() {
    size_t initial_item_allocation = nondet_size_t();
    size_t item_size = nondet_size_t();
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, initial_item_allocation, item_size);
    return list;
}

struct aws_array_list *make_bounded_array_list(size_t max_initial_item_allocation, size_t max_item_size) {
    size_t initial_item_allocation = nondet_size_t();
    __CPROVER_assume(initial_item_allocation <= max_initial_item_allocation);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= max_item_size);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, initial_item_allocation, item_size);
    return list;
}

int compare(const void *a, const void *b) {
    size_t n = nondet_size_t();
    __CPROVER_assume(n <= MAX_ITEM_SIZE);
    __CPROVER_precondition(__CPROVER_r_ok(a, n), "first element readable in compare function");
    __CPROVER_precondition(__CPROVER_r_ok(b, n), "second element readable in compare function");
    return nondet_int();
}
