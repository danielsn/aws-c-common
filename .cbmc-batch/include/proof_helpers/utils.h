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

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

struct store_byte_from_buffer {
    size_t index;
    uint8_t byte;
};

void assert_bytes_match(const uint8_t *a, const uint8_t *b, size_t len);
void assert_all_bytes_are(const uint8_t *a, const uint8_t c, size_t len);
void assert_all_zeroes(const uint8_t *a, size_t len);
bool isPowerOfTwo(size_t x);
void save_byte_from_array(uint8_t* array, size_t size, struct store_byte_from_buffer *storage);
void save_byte_from_hash_table(struct aws_hash_table* map, struct store_byte_from_buffer* storage);
void check_byte_from_hash_table(struct aws_hash_table* map, struct store_byte_from_buffer* storage);
