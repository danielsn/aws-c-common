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

#include <aws/common/array_list.h>
#include <aws/common/byte_buf.h>
#include <aws/common/common.h>
#include <aws/common/string.h>

/**
 * Makes a byte_buf, with as much nondet as possible, defined len and capacity
 */
void make_arbitrary_byte_buf(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t capacity, size_t len);

/**
 * Makes a byte_buf, with as much nondet as possible, len = capacity
 */
void make_arbitrary_byte_buf_full(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t capacity);

/**
 * Makes a valid header, with as much nondet as possible, nondet len
 */
void make_arbitrary_byte_buf_nondet_len(struct aws_allocator *allocator, struct aws_byte_buf *buf);

/**
 * Makes a valid header, with as much nondet as possible, nondet len <= max
 */
void make_arbitrary_byte_buf_nondet_len_max(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t max);
struct aws_byte_buf * allocate_arbitrary_byte_buf_nondet_len_max(struct aws_allocator *allocator, size_t max);


/**
 * Makes a valid array_list, with as much nondet as possible, initial_item_allocation in size
 */
void make_arbitrary_list(struct aws_array_list *AWS_RESTRICT list,
			 struct aws_allocator *alloc,
			 size_t initial_item_allocation,
			 size_t item_size);

struct aws_string* make_arbitrary_aws_string(struct aws_allocator *allocator, size_t size);
struct aws_string* make_arbitrary_aws_string_nondet_len(struct aws_allocator *allocator);
struct aws_string* make_arbitrary_aws_string_nondet_len_with_max(struct aws_allocator *allocator, size_t max);
