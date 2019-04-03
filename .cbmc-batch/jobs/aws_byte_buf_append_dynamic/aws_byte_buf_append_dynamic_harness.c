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

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

bool is_bounded_byte_buf(struct aws_byte_buf *buf, size_t max_size) {
    return buf->capacity == max_size;
}

bool is_valid_byte_buf(struct aws_byte_buf *buf) {
    return (buf->len <= buf->capacity)
    && (buf->allocator == NULL || buf->allocator == can_fail_allocator());
    /* TODO: once we can check allocated size of buffer, also assert that
     * buf->capacity <= __CPROVER_buffer_size(buf->buffer);
     */
}

void ensure_bute_buf_has_allocated_buffer_member(struct aws_byte_buf *buf) {
    __CPROVER_assume(buf->capacity <= MAX_MALLOC);
    buf->buffer = malloc(sizeof(*(buf->buffer)) * buf->capacity);
}

bool is_bounded_byte_cursor(struct aws_byte_cursor *cursor, size_t max_size) {
    return cursor->len <= max_size;
}

bool is_valid_byte_cursor(struct aws_byte_cursor *cursor) {
    return (cursor->ptr == NULL && cursor->len == 0)
    || (cursor->ptr != NULL && cursor->len != 0);
    /* TODO: once we can check allocated size of buffer, also assert that
     * cursor->len <= __CPROVER_buffer_size(cursor->ptr);
     */
}

void ensure_byte_cursor_has_allocated_buffer_member(struct aws_byte_cursor *cursor) {
    __CPROVER_assume(cursor->len <= MAX_MALLOC);
    cursor->ptr = malloc(cursor->len);
}

void aws_byte_buf_append_dynamic_harness() {
    /* new proof style */
    struct aws_byte_buf to;
    __CPROVER_assume(is_bounded_byte_buf(&to, MAX_MALLOC));
    __CPROVER_assume(is_valid_byte_buf(&to));
    ensure_bute_buf_has_allocated_buffer_member(&to);

    struct aws_byte_cursor from;
    __CPROVER_assume(is_bounded_byte_cursor(&from, MAX_MALLOC));
    __CPROVER_assume(is_valid_byte_cursor(&from));
    ensure_byte_cursor_has_allocated_buffer_member(&from);

    aws_byte_buf_append_dynamic(&to, &from);

    assert(is_valid_byte_buf(&to));
    assert(is_valid_byte_cursor(&from));
}
