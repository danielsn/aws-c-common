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
void aws_hash_table_move_harness() {
    struct aws_hash_table map_a;
    struct aws_hash_table map_b;

    ensure_allocated_hash_table(&map_a, MAX_TABLE_SIZE);
    ensure_allocated_hash_table(&map_b, MAX_TABLE_SIZE);
    __CPROVER_assume(is_valid_hash_table(&map_a));
    __CPROVER_assume(is_valid_hash_table(&map_b));

    //Check what happens if the to and from alias.
    struct aws_hash_table* pa = &map_a;
    struct aws_hash_table* pb = &map_b;//nondet_bool() ? &map_a : &map_b;

    struct store_byte_from_buffer byte_b;
    save_byte_from_hash_table(pb, &byte_b);
    
    aws_hash_table_move(pa, pb);

    //Ensure that the destination table is valid.
    assert(is_valid_hash_table(pa));
    
    //Ensure that the two tables were byte for byte swapped
    check_byte_from_hash_table(pa, &byte_b);
}
