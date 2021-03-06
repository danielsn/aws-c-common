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
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_byte_buf_cat_harness() {
    /* parameters */
    struct aws_byte_buf buffer1;
    struct aws_byte_buf buffer2;
    struct aws_byte_buf buffer3;
    struct aws_byte_buf dest;
    size_t number_of_args = 3;

    /* assumptions */
    __CPROVER_assume(aws_byte_buf_is_bounded(&buffer1, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buffer1);
    __CPROVER_assume(aws_byte_buf_is_valid(&buffer1));
    __CPROVER_assume(aws_byte_buf_is_bounded(&buffer2, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buffer2);
    __CPROVER_assume(aws_byte_buf_is_valid(&buffer2));
    __CPROVER_assume(aws_byte_buf_is_bounded(&buffer3, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buffer3);
    __CPROVER_assume(aws_byte_buf_is_valid(&buffer3));
    ensure_byte_buf_has_allocated_buffer_member(&dest);
    __CPROVER_assume(aws_byte_buf_is_valid(&dest));

    /* save current state of the data structure */
    struct aws_byte_buf old_buffer1 = buffer1;
    struct store_byte_from_buffer old_byte_from_buffer1;
    save_byte_from_array(buffer1.buffer, buffer1.len, &old_byte_from_buffer1);
    struct aws_byte_buf old_buffer2 = buffer2;
    struct store_byte_from_buffer old_byte_from_buffer2;
    save_byte_from_array(buffer2.buffer, buffer2.len, &old_byte_from_buffer2);
    struct aws_byte_buf old_buffer3 = buffer3;
    struct store_byte_from_buffer old_byte_from_buffer3;
    save_byte_from_array(buffer3.buffer, buffer3.len, &old_byte_from_buffer3);
    struct aws_byte_buf old_dest = dest;
    struct store_byte_from_buffer old_byte_from_dest;
    save_byte_from_array(dest.buffer, dest.len, &old_byte_from_dest);

    /* operation under verification */
    if (aws_byte_buf_cat(
            nondet_bool() ? &dest : NULL,
            number_of_args,
            nondet_bool() ? &buffer1 : NULL,
            nondet_bool() ? &buffer2 : NULL,
            nondet_bool() ? &buffer3 : NULL) == AWS_OP_SUCCESS) {
        assert((old_dest.capacity - old_dest.len) >= (buffer1.len + buffer2.len + buffer3.len));
    } else {
        assert((old_dest.capacity - old_dest.len) < (buffer1.len + buffer2.len + buffer3.len));
    }

    /* assertions */
    assert(aws_byte_buf_is_valid(&buffer1));
    assert(aws_byte_buf_is_valid(&buffer2));
    assert(aws_byte_buf_is_valid(&buffer3));
    assert(aws_byte_buf_is_valid(&dest));
    assert_byte_buf_equivalence(&buffer1, &old_buffer1, &old_byte_from_buffer1);
    assert_byte_buf_equivalence(&buffer2, &old_buffer2, &old_byte_from_buffer2);
    assert_byte_buf_equivalence(&buffer3, &old_buffer3, &old_byte_from_buffer3);
}
