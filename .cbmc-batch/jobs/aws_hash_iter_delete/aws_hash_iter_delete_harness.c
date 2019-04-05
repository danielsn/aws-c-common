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

bool has_an_empty_slot(struct aws_hash_table* map)
{
  struct hash_table_state* state = map->p_impl;
  size_t index;
  __CPROVER_assume(index < state->size);
  return state->slots[index].hash_code == 0;
}

/**
 * Runtime: 4.5s
 */
void aws_hash_iter_delete_harness() {
  
    struct aws_hash_table map;
    ensure_allocated_hash_table(&map, MAX_TABLE_SIZE);
    __CPROVER_assume(is_valid_hash_table(&map));
    __CPROVER_assume(has_an_empty_slot(&map));
    
    struct aws_hash_iter iter;
    iter.map = &map;
    __CPROVER_assume(aws_hash_iter_is_valid(&iter));
      
    struct store_byte_from_buffer old_byte;
    save_byte_from_hash_table(&map, &old_byte);

    aws_hash_iter_delete(&iter, false);
    
    assert(aws_hash_iter_is_valid(&iter));
    assert(is_valid_hash_table(&map));
    check_byte_from_hash_table(&map, &old_byte);
}
