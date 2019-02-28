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
#include <aws/cryptosdk/cache.h>
#include <aws/cryptosdk/cipher.h>
#include <aws/cryptosdk/edk.h>
#include <aws/cryptosdk/private/cipher.h>
#include <aws/cryptosdk/private/header.h>
#include <stddef.h>
#include <stdint.h>

/**
 * Makes a valid header, with as much nondet as possible
 */
struct aws_cryptosdk_hdr* make_header(struct aws_allocator * allocator, bool init_edk_list);

/**
 * Makes a valid header, with as much nondet as possible
 */
void make_arbitrary_edk(struct aws_allocator *allocator, struct aws_cryptosdk_edk *edk);

/**
 * Makes a list of edk, with as much nondet as possible
 */
void make_arbitrary_edk_list(struct aws_array_list *AWS_RESTRICT list,
			     struct aws_allocator *alloc,
			     size_t initial_item_allocation);

/**
 * Makes a alg property, with as much nondet as possible
 */
void make_arbitrary_alg_properties(struct aws_cryptosdk_alg_properties *props);
#define MSG_ID_LEN 16

struct aws_cryptosdk_mat_cache* make_arbitrary_aws_cryptosdk_mat_cache(struct aws_allocator *alloc, size_t capacity);
