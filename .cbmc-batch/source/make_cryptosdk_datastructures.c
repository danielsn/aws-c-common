/*
 * Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include "cbmcproof/cbmc_nondet.h"
#include "cbmcproof/hash_table_model.h"
#include "cbmcproof/libcrypto_overrides.h"
#include "cbmcproof/make_common_datastructures.h"
#include "cbmcproof/make_cryptosdk_datastructures.h"
#include <aws/common/hash_table.h>
#include <aws/cryptosdk/cache.h>
#include <aws/cryptosdk/private/cipher.h>
#include <aws/cryptosdk/private/local_cache.h>
#include <openssl/evp.h>
#include <stdlib.h>


#define MAX_AAD_COUNT 1
#define MAX_BUFFER_LEN 1
#define MAX_EDK_COUNT 1

/*
struct aws_cryptosdk_hdr {
    struct aws_allocator *alloc;

    uint16_t alg_id;

    uint32_t frame_len;

    struct aws_byte_buf iv, auth_tag;

    uint8_t message_id[MESSAGE_ID_LEN];

    // aws_string * -> aws_string *
    struct aws_hash_table enc_context;
    struct aws_array_list edk_list;

    // number of bytes of header except for IV and auth tag,
    // i.e., exactly the bytes that get authenticated
    size_t auth_len;
};
*/
#define HASH_TABLE_SIZE 4
#define EDK_LIST_SIZE 4


//static function in header.c
int aws_cryptosdk_algorithm_is_known(uint16_t alg_id);

void make_arbitrary_byte_buf(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t capacity, size_t len) {
  buf->buffer = malloc(capacity);//use malloc because we will need to deallocate later
    buf->len = len;
    buf->capacity = capacity;
    buf->allocator = allocator;
}

void make_arbitrary_byte_buf_full(struct aws_allocator *allocator, struct aws_byte_buf *buf, size_t capacity) {
  make_arbitrary_byte_buf(allocator, buf, capacity, capacity);
}

void make_arbitrary_byte_buf_nondet_len(struct aws_allocator *allocator, struct aws_byte_buf *buf)
{
  size_t capacity = nondet_size_t();
  size_t len = nondet_size_t();
  __CPROVER_assume(len <= capacity);
  make_arbitrary_byte_buf(allocator, buf, capacity, len);
}

/*
struct aws_array_list {
    struct aws_allocator *alloc;
    size_t current_size;
    size_t length;
    size_t item_size;
    void *data;
};
*/

//based off of https://github.com/awslabs/aws-c-common/blob/master/include/aws/common/array_list.inl
//aws_array_list_init_dynamic
void make_arbitrary_list(struct aws_array_list *AWS_RESTRICT list,
			struct aws_allocator *alloc,
			size_t initial_item_allocation,
			size_t item_size) {
  list->alloc = alloc;
  size_t allocation_size = initial_item_allocation * item_size;
  list->current_size = allocation_size;
  //  list->length = nondet_size_t();
  list->length = initial_item_allocation;//DSN HACK FOR NOW UNTIL we can use nondet with the constant propegator
  __CPROVER_assume(list->length >=0 && list->length <= initial_item_allocation);
  size_t dsn_len = list->length;
  list->item_size = item_size;
  //since we want an allocation that can never fail, use straight malloc here
  list->data = malloc(allocation_size);//allocation_size > 0 ? malloc(allocation_size) : NULL;
  uint8_t* dsn_data = list->data;
}

void make_arbitrary_edk(struct aws_allocator *allocator, struct aws_cryptosdk_edk *edk)
{
  make_arbitrary_byte_buf_nondet_len(allocator, &edk->provider_id);
  make_arbitrary_byte_buf_nondet_len(allocator, &edk->provider_info);
  make_arbitrary_byte_buf_nondet_len(allocator, &edk->ciphertext);
}

void make_arbitrary_edk_list(struct aws_array_list *AWS_RESTRICT list,
			     struct aws_allocator *alloc,
			     size_t initial_item_allocation) {
  make_arbitrary_list(list, alloc, initial_item_allocation, sizeof(struct aws_cryptosdk_edk));
  struct aws_cryptosdk_edk *edk;
   for (int i = 0; i < list->length; ++i){
     aws_array_list_get_at_ptr(list, (void**)&edk, i);
     make_arbitrary_edk(alloc, edk);
   }
}

struct aws_cryptosdk_hdr* make_header(struct aws_allocator * allocator, bool init_edk_list) {
  struct aws_cryptosdk_hdr* hdr = __CPROVER_allocate(sizeof(*hdr), 0);
  uint16_t dummy_16;
  struct aws_cryptosdk_hdr dummy = {
	  .alloc = allocator,
	  .alg_id = ALG_AES256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384,
	  //	  .frame_len = nondet_uint32(),
	  .iv =
	  {
	   //	   .len = nondet_size_t(),
	   //	   .buffer = NULL,
	   //	   .capacity = nondet_size_t(),
	   .allocator = allocator
	  },
	  .auth_tag =
	  {
	   //	   .len = nondet_size_t(),
	   //	   .buffer = NULL,
	   //	   .capacity = nondet_size_t(),
	   .allocator = allocator
	  },
	  .edk_list =
	  {
	   .alloc = allocator
	  }
  };
  *hdr = dummy;
    //hdr->alg_id = dummy_16;
  //leave ag_id nondet
  //leave frame_len nondet
  //We need to assume that the header has a valid iv and auth_tag.  These tags are set
  //at various places in code - might make sense to check them during use?
  // https://github.com/awslabs/aws-encryption-sdk-c/blob/d3ce77c83d1b96393e037ddfb32035062b325411/source/session_encrypt.c#L140
  //also several places in parsing, but those all appear to be checked for validity
  __CPROVER_assume(aws_cryptosdk_algorithm_is_known(hdr->alg_id));
  //leave iv, auth_tag nondet, but with the expected size
  make_arbitrary_byte_buf_full(allocator, &hdr->iv, aws_cryptosdk_algorithm_ivlen(hdr->alg_id));
  make_arbitrary_byte_buf_full(allocator, &hdr->auth_tag, aws_cryptosdk_algorithm_taglen(hdr->alg_id));
  //leave message_id nondet
  make_arbitrary_hash_table(&hdr->enc_ctx, allocator, HASH_TABLE_SIZE, make_hash_elem_awsstring_awsstring );
  if(init_edk_list) {
    make_arbitrary_edk_list(&hdr->edk_list, allocator, EDK_LIST_SIZE);
  } else {
    make_arbitrary_list(&hdr->edk_list, allocator, EDK_LIST_SIZE, sizeof(struct aws_cryptosdk_edk));
  }
  //leave auth_len nondet
  return hdr;
}

const EVP_MD *override_EVP_MD_ptr(void){
  return nondet_int() ? malloc(sizeof(EVP_MD)) : NULL;
}

const EVP_CIPHER *override_EVP_CIPHER_ptr(void){
  return nondet_int() ? malloc(sizeof(EVP_CIPHER)) : NULL;
}

/* struct aws_cryptosdk_alg_properties { */
/*     const char *md_name, *cipher_name, *alg_name; */

/*     /\** */
/*      * Pointer to a structure containing crypto-backend-specific */
/*      * information. This is a forward-declared structure to keep it */
/*      * opaque to backend-independent code */
/*      *\/ */
/*     const struct aws_cryptosdk_alg_impl *impl; */

/*     size_t data_key_len, content_key_len, iv_len, tag_len, signature_len; */

/*     enum aws_cryptosdk_alg_id alg_id; */
/* }; */


void make_arbitrary_alg_properties(struct aws_cryptosdk_alg_properties *props)
{
  props->impl = malloc(sizeof(struct aws_cryptosdk_alg_impl));
  struct aws_cryptosdk_alg_impl impl =
    {
     .md_ctor = nondet_int() ? NULL : override_EVP_MD_ptr,
     .cipher_ctor = nondet_int() ? NULL : override_EVP_CIPHER_ptr,
    };
  *(struct aws_cryptosdk_alg_impl*)(props->impl) = impl;
  __CPROVER_assume(props->data_key_len <= MAX_DATA_KEY_SIZE);
}


extern const struct aws_cryptosdk_mat_cache_vt local_cache_vt;
const size_t HASH_CACHE_ID_SIZE = 8;
const size_t MAX_KEY_MATERIALS_LEN = 2048;
const size_t MAX_MAT_CACHE_HASH_TABLE_LEN = 8;

void make_arbitrary_local_cache_entry(struct aws_allocator *alloc, struct local_cache_entry* entry, struct aws_cryptosdk_local_cache *owner)
{
  entry->owner = owner;
  make_arbitrary_byte_buf_full(alloc, &entry->cache_id, HASH_CACHE_ID_SIZE);
  entry->enc_materials = nondet_bool() ? NULL : malloc(sizeof *entry->enc_materials);
  entry->dec_materials = nondet_bool() ? NULL : malloc(sizeof *entry->dec_materials);
}

struct local_cache_entry* allocate_arbitrary_local_cache_entry(struct aws_allocator *alloc, struct aws_cryptosdk_local_cache *owner)
{
  struct local_cache_entry* entry = malloc(sizeof(*entry));
  make_arbitrary_local_cache_entry(alloc, entry, owner);
  return entry;
}

struct aws_cryptosdk_mat_cache* make_arbitrary_aws_cryptosdk_mat_cache(struct aws_allocator *alloc, size_t capacity)
{
  struct aws_cryptosdk_local_cache *cache = malloc(sizeof(*cache));
  aws_cryptosdk_mat_cache_base_init(&cache->base, &local_cache_vt);
  cache->allocator     = alloc;
  cache->lru_head.next = cache->lru_head.prev = &cache->lru_head;
  cache->capacity                             = capacity;
  cache->clock_get_ticks                      = aws_sys_clock_get_ticks;
  aws_mutex_init(&cache->mutex); //DSN should I assume this succeeds?
  //cache->entries is a hash table mapping bytebuf -> local_cache_entry
  //make_arbitrary_hash_table(&cache->entries, MAX_MAT_CACHE_HASH_TABLE_LEN, 


  return NULL;

}
