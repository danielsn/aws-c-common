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

/**
 * Runtime: 4.5s
 */
void aws_hash_table_get_entry_count_harness() {
    struct aws_hash_table map;

    ensure_allocated_hash_table(&map, MAX_TABLE_SIZE);
    __CPROVER_assume(is_valid_hash_table(&map));

    struct store_byte_from_buffer old_byte;
    save_byte_from_hash_table(&map, &old_byte);
    
    size_t entry_count = aws_hash_table_get_entry_count(&map);
    struct hash_table_state* state = map.p_impl;

    //Check that we have the correct return value
    assert(entry_count == state->entry_count);
    //Ensure that it is still a valid hash_table.
    assert(is_valid_hash_table(&map));
    //Ensure that the table didn't change
    check_byte_from_hash_table(&map, &old_byte);
}
