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

const int MAX_TABLE_SIZE = 16;

void aws_hash_table_init_harness() {
    struct aws_allocator *allocator;
    ASSUME_DEFAULT_ALLOCATOR(allocator);
    size_t size;
    __CPROVER_assume(size <= MAX_TABLE_SIZE);

    aws_hash_fn *hash_fn;
    aws_hash_callback_eq_fn *equals_fn;
    aws_hash_callback_destroy_fn *destroy_key_fn;
    aws_hash_callback_destroy_fn *destroy_value_fn;   
    struct aws_hash_table map;
    int rval = aws_hash_table_init
      (&map,
       allocator,
       size,
       hash_fn,
       equals_fn,
       destroy_key_fn,
       destroy_value_fn);
    //asserting things about the resulting hash_table
    //would require looking inside the abstraction
    
}
