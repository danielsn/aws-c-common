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

/**
 * Makes a valid header, but with as much nondet as possible
 */
struct aws_cryptosdk_hdr* make_header(struct aws_allocator * allocator, bool init_edk_list);

void make_arbitrary_byte_buf(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t capacity, size_t len);

void make_arbitrary_byte_buf_full(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t capacity);

void make_arbitrary_byte_buf_nondet_len(struct aws_allocator *allocator, struct aws_byte_buf *buf);

void make_arbitrary_list(struct aws_array_list *AWS_RESTRICT list,
			struct aws_allocator *alloc,
			size_t initial_item_allocation,
			 size_t item_size);

void make_arbitrary_edk(struct aws_allocator *allocator, struct aws_cryptosdk_edk *edk);

void make_arbitrary_edk_list(struct aws_array_list *AWS_RESTRICT list,
			     struct aws_allocator *alloc,
			     size_t initial_item_allocation);
