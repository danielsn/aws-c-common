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
/** 
 * Abstract memcpy to check that pointers are valid, and then return dst
 * Doesn't actually copy the bytes - if the underlying array was already nondet, that is fine
 * If it wasn't, this might be unsound. 
 */
void *memset_impl(void *s, int c, size_t n)
{
  __CPROVER_precondition(__CPROVER_w_ok(s, n),
                         "memset destination region writeable");
  if(n > 0)
  {
    //DSN TODO proper assignment here 
    //char *sp=s;
    //for(__CPROVER_size_t i=0; i<n ; i++) sp[i]=c;
    //    unsigned char s_n[n];
    //    __CPROVER_array_set(s_n, (unsigned char)c);
    //    __CPROVER_array_replace((unsigned char *)s, s_n);
  }
  return s;
}

void *memset(void *s, int c, size_t n)
{
  return memset_impl(s,c,n);
}

void *__builtin___memset_chk(void *s, int c, size_t n, size_t os)
{
  (void) os;
  return memset_impl(s,c,n);
}
