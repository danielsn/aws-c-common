/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/byte_buf.h>
#include <aws/common/ring_buffer.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_ring_buffer_acquire_up_to_harness() {
    /* parameters */
    struct aws_ring_buffer ring_buf;
    size_t ring_buf_size;
    size_t requested_size;
    size_t minimum_size;
    struct aws_byte_buf buf;

    /* assumptions */
    ensure_ring_buffer_has_allocated_members(&ring_buf, ring_buf_size);
    __CPROVER_assume(aws_ring_buffer_is_valid(&ring_buf));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));
    __CPROVER_assume(requested_size >= minimum_size);

    if (aws_ring_buffer_acquire_up_to(&ring_buf, minimum_size, requested_size, &buf) == AWS_OP_SUCCESS) {
        /* assertions */
        assert(aws_ring_buffer_is_valid(&ring_buf));
        assert(aws_byte_buf_is_valid(&buf));
        assert(buf.capacity >= minimum_size && buf.capacity <= requested_size);
        assert(buf.len == 0); /* aws_byte_buf always created with aws_byte_buf_from_empty_array */
        assert(aws_ring_buffer_buf_belongs_to_pool(&ring_buf, &buf));
    }
}
