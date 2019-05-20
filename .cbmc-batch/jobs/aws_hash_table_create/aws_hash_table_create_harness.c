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
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

int s_expand_table(struct aws_hash_table *map) {
    struct hash_table_state *old_state = map->p_impl;
    struct hash_table_state template = *old_state;

    s_update_template_size(&template, template.size * 2);

    struct hash_table_state *new_state = s_alloc_state(&template);
    if (!new_state) {
        return AWS_OP_ERR;
    }

    map->p_impl = new_state;
    aws_mem_release(new_state->alloc, old_state);
    __CPROVER_assume(aws_hash_table_is_valid(map));
    size_t empty_slot_idx;
    __CPROVER_assume(aws_hash_table_has_an_empty_slot(&map, &empty_slot_idx));
    return AWS_OP_SUCCESS;
}
void aws_hash_table_create_harness() {
    struct aws_hash_table map;
    ensure_allocated_hash_table(&map, MAX_TABLE_SIZE);
    __CPROVER_assume(aws_hash_table_is_valid(&map));
    map.p_impl->equals_fn = uninterpreted_equals;
    map.p_impl->hash_fn = uninterpreted_hasher;
    map.p_impl->alloc = can_fail_allocator();

    size_t empty_slot_idx;
    __CPROVER_assume(aws_hash_table_has_an_empty_slot(&map, &empty_slot_idx));

    void *key;
    struct aws_hash_element *p_elem;
    int was_created;

    aws_hash_table_create(&map, key, nondet_bool() ? &p_elem : NULL, nondet_bool() ? &was_created : NULL);

    assert(aws_hash_table_is_valid(&map));
}
