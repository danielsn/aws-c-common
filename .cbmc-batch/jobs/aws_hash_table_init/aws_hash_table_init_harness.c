/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/hash_table.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

struct hash_table_entry {
    struct aws_hash_element element;
    uint64_t hash_code; /* hash code (0 signals empty) */
};

struct hash_table_state {
    aws_hash_fn *hash_fn;
    aws_hash_callback_eq_fn *equals_fn;
    aws_hash_callback_destroy_fn *destroy_key_fn;
    aws_hash_callback_destroy_fn *destroy_value_fn;
    struct aws_allocator *alloc;

    size_t size, entry_count;
    size_t max_load;
    /* We AND a hash value with mask to get the slot index */
    size_t mask;
    double max_load_factor;
    /* actually variable length */
    struct hash_table_entry slots[1];
};

/* Function to check if x is power of 2 */
bool isPowerOfTwo(int x) {
    /* First x in the below expression is for the case when x is 0 */
    return x && (!(x & (x - 1)));
}

bool is_valid_hash_table_state(struct hash_table_state *map) {
    return map->hash_fn != NULL && map->equals_fn != NULL &&
           //    map->destroy_key_fn != NULL &&
           //    map->destroy_value_fn != NULL &&
           map->alloc != NULL && isPowerOfTwo(map->size) && map->mask == (map->size - 1) &&
           map->entry_count <= map->size && map->max_load < map->size &&
           map->max_load_factor == 0.95; // currently hardcoded
}

/**
 * Runtime: user	10m12.757s (table size 4)
 * 0.78 (121 lines out of 156 statically-reachable lines in 17 functions reached)
 * The low coverage is due to various overflow checking that statically cannot
 * happen in this harness.
 */
void aws_hash_table_init_harness() {
    struct aws_allocator *allocator;
    ASSUME_CAN_FAIL_ALLOCATOR(allocator);
    size_t size;
    __CPROVER_assume(size <= MAX_TABLE_SIZE);

    aws_hash_fn *hash_fn;
    aws_hash_callback_eq_fn *equals_fn;
    aws_hash_callback_destroy_fn *destroy_key_fn;
    aws_hash_callback_destroy_fn *destroy_value_fn;
    struct aws_hash_table map;
    int rval = aws_hash_table_init(&map, allocator, size, hash_fn, equals_fn, destroy_key_fn, destroy_value_fn);
    if (rval) {
        assert(is_valid_hash_table_state(&map));
    }
}
