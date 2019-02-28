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

#include <stddef.h>
#include "cbmcproof/cbmc_nondet.h"
#define NONDET_THIS_MANY_BYTES 8
#define UNROLL_THIS_MANY_BYTES 32
/** 
 * Abstract memcpy to check that pointers are valid, and then return dst
 * Doesn't actually copy the bytes - if the underlying array was already nondet, that is fine
 * If it wasn't, this might be unsound. 
 */
void* memcpy_impl( void * dst, const void * src, size_t n )
{
  __CPROVER_precondition(
    __CPROVER_POINTER_OBJECT(dst) != __CPROVER_POINTER_OBJECT(src) ||
      ((const char *)src >= (const char *)dst + n) ||
      ((const char *)dst >= (const char *)src + n),
    "memcpy src/dst overlap");
  __CPROVER_precondition(
    __CPROVER_r_ok(src, n), "memcpy source region readable");
  __CPROVER_precondition(
    __CPROVER_w_ok(dst, n), "memcpy destination region writeable");

#if 0
  if(n > 0) {
    //for(__CPROVER_size_t i=0; i<n ; i++) ((char *)dst)[i]=((const char *)src)[i];
    char src_n[n];
    __CPROVER_array_copy(src_n, (char *)src);
    __CPROVER_array_replace((char *)dst, src_n);
  }
#endif

#if 1
  for(__CPROVER_size_t i=0; i<n && i < UNROLL_THIS_MANY_BYTES ; ++i) ((char *)dst)[i]=((const char *)src)[i];
#endif
 
#if 0
  uint8_t* dst_b = (uint8_t *)dst;
  uint8_t* src_b = (uint8_t *)src;

  for (int i = 0; i < UNROLL_THIS_MANY_BYTES; ++i){
    dst_b[i] = 0;//src_b[i];
  }
#endif
  
#if 0
  for (int i = 0; i < NONDET_THIS_MANY_BYTES; ++i){
    size_t loc = nondet_size_t();
    __CPROVER_assume(loc < n);
    dst_b[loc] = nondet_uint8_t();
  }
#endif

  return dst;
}

void * memcpy ( void * dst, const void * src, size_t n )
{
  return memcpy_impl(dst,src,n);
}

void *__builtin___memcpy_chk(void *dst, const void *src, __CPROVER_size_t n, __CPROVER_size_t size)
{
  (void) size;
  return memcpy_impl(dst,src,n);

}
