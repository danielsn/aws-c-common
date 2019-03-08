#ifndef AWS_COMMON_MATH_H
#define AWS_COMMON_MATH_H

/*
 * Copyright 2010-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/common.h>
#include <aws/common/config.h>

#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Fall back to the pure-C implementations */
#include <aws/common/math.fallback.inl>


/**
 * Multiplies a * b. If the result overflows, returns SIZE_MAX.
 */
AWS_STATIC_IMPL size_t aws_mul_size_saturating(size_t a, size_t b) {
#if SIZE_MAX == UINT32_MAX
    return (size_t)aws_mul_u32_saturating(a, b);
#elif SIZE_MAX == UINT64_MAX
    return (size_t)aws_mul_u64_saturating(a, b);
#else
#    error "Target not supported"
#endif
}

/**
 * Multiplies a * b and returns the result in *r. If the result
 * overflows, returns AWS_OP_ERR; otherwise returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_mul_size_checked(size_t a, size_t b, size_t *r) {
#if SIZE_MAX == UINT32_MAX
    return aws_mul_u32_checked(a, b, (uint32_t *)r);
#elif SIZE_MAX == UINT64_MAX
    return aws_mul_u64_checked(a, b, (uint64_t *)r);
#else
#    error "Target not supported"
#endif
}

/**
 * Adds a + b.  If the result overflows returns SIZE_MAX.
 */
AWS_STATIC_IMPL size_t aws_add_size_saturating(size_t a, size_t b) {
#if SIZE_MAX == UINT32_MAX
    return (size_t)aws_add_u32_saturating(a, b);
#elif SIZE_MAX == UINT64_MAX
    return (size_t)aws_add_u64_saturating(a, b);
#else
#    error "Target not supported"
#endif
}

/**
 * Adds a + b and returns the result in *r. If the result
 * overflows, returns AWS_OP_ERR; otherwise returns AWS_OP_SUCCESS.
 */

AWS_STATIC_IMPL int aws_add_size_checked(size_t a, size_t b, size_t *r) {
#if SIZE_MAX == UINT32_MAX
    return aws_add_u32_checked(a, b, (uint32_t *)r);
#elif SIZE_MAX == UINT64_MAX
    return aws_add_u64_checked(a, b, (uint64_t *)r);
#else
#    error "Target not supported"
#endif
}

#ifdef __cplusplus
}
#endif

#endif /* AWS_COMMON_MATH_H */
