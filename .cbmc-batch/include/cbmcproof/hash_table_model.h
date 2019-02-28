/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#pragma once
#include <aws/common/hash_table.h>
#include <stddef.h>
#include <stdint.h>

typedef void(*ElemMaker)(struct aws_hash_element* elem, const struct aws_hash_table *map);
void make_arbitrary_hash_table(struct aws_hash_table *map, struct aws_allocator* alloc, size_t size, ElemMaker elem_maker);
void make_hash_elem_awsstring_awsstring(struct aws_hash_element* elem, const struct aws_hash_table *map);
void make_hash_elem_bytebuf_local_cache_entry(struct aws_hash_element* elem, const struct aws_hash_table *map);
