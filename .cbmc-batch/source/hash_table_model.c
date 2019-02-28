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

#include "cbmcproof/hash_table_model.h"
#include "cbmcproof/macros.h"
#include "cbmcproof/make_common_datastructures.h"
#include "cbmcproof/make_cryptosdk_datastructures.h"
#include "cbmcproof/proof_allocators.h"
#include <aws/common/hash_table.h>
#include <aws/common/string.h>
#include <limits.h>
#include <stdbool.h>

// This is a simple model of a hash table, in which operations test where inputs are valid
// and then take non-determinstic action.  It should be sufficient for memory-safety proofs
// but we might need something stronger for functional correctness proofs.

struct hash_table_state {
  struct aws_allocator* alloc;
  bool was_init;
  bool was_cleaned_up;
  size_t size;
  size_t entry_count;
  ElemMaker elem_maker;
}; 


//struct hash_table_state {
//    aws_hash_fn *hash_fn;
//    aws_equals_fn *equals_fn;
//    aws_hash_element_destroy_fn *destroy_key_fn;
//    aws_hash_element_destroy_fn *destroy_value_fn;
//    struct aws_allocator *alloc;
//
//    size_t size, entry_count;
//    size_t max_load;
//    /* We AND a hash value with mask to get the slot index */
//    size_t mask;
//    double max_load_factor;
//    /* actually variable length */
//    struct hash_table_entry slots[1];
//};


//Thoughts on interresting properties to track:
// Init happened
// Memory allocated
// not-cleaned-up
// size? Do I want this to be nondet?

#define CBMC_CHECK_POINTER( ptr ) (void)*(char *)ptr

/*
struct aws_hash_element {
    const void *key;
    void *value;
};
*/
void make_hash_elem_awsstring_awsstring(struct aws_hash_element* elem, const struct aws_hash_table *map)
{
  struct hash_table_state* state = map->p_impl;
  *(void**)&elem->key = make_arbitrary_aws_string_nondet_len(state->alloc);
  elem->value = make_arbitrary_aws_string_nondet_len(state->alloc);
}

const size_t HASH_CACHE_ID_SIZE = 8;
/* void make_hash_elem_bytebuf_local_cache_entry(struct aws_hash_element* elem, const struct aws_hash_table *map) */
/* { */
/*   struct hash_table_state* state = map->p_impl; */
/*   struct aws_byte_buf * tempbuf = 0; */

/*   //allocate_arbitrary_byte_buf_nondet_len_max(state->alloc, HASH_CACHE_ID_SIZE); */
/*   *(char**)(&elem->key) = allocate_arbitrary_byte_buf_nondet_len_max(state->alloc, HASH_CACHE_ID_SIZE); */
/*   elem->value =  allocate_arbitrary_local_cache_entry */
/*     (state->alloc, */
/*      entry, */
/*      //DSN figure out how to track this info to here if needed instead of using nondet */
/*      nondet_bool() ? NULL : nondet_voidp()); */
/* } */


void make_arbitrary_hash_table(struct aws_hash_table *map, struct aws_allocator* alloc, size_t size, ElemMaker elem_maker)
{
  struct hash_table_state* impl =__CPROVER_allocate(sizeof(struct hash_table_state),0);
  impl->alloc = alloc;
  impl->was_init = true;
  impl->was_cleaned_up = false;
  impl->size = size;
  __CPROVER_assume(impl->entry_count >= 0 && impl->entry_count < impl->size);
  impl->elem_maker = elem_maker;
  map->p_impl = impl;
}

/**
 * Initializes a hash map with initial capacity for 'size' elements
 * without resizing. Uses hash_fn to compute the hash of each element.
 * equals_fn to compute equality of two keys.  Whenver an elements is
 * removed without being returned, destroy_key_fn is run on the pointer
 * to the key and destroy_value_fn is run on the pointer to the value.
 * Either or both may be NULL if a callback is not desired in this case.
 */
int aws_hash_table_init(
    struct aws_hash_table *map,
    struct aws_allocator *alloc,
    size_t size,
    aws_hash_fn *hash_fn,
    aws_hash_callback_eq_fn *equals_fn,
    aws_hash_callback_destroy_fn *destroy_key_fn,
    aws_hash_callback_destroy_fn *destroy_value_fn)
{
  CBMC_CHECK_PTR(map);
  CBMC_CHECK_PTR(alloc);
  //For now, just check that the functions are non-null.  Not much more we can do without specs
  assert(hash_fn);
  assert(equals_fn);
  assert(0);//If we actually use this function, I'll need to add a trick to figure out
  //the hash-elem-maker from the hash_fn pointer.
  //The last two function pointers may be null according to the spec
  //make_arbitrary_hash_table(map,size);
  return nondet_int();
}

			      

/**
 * Deletes every element from map and frees all associated memory.
 * destroy_fn will be called for each element.  aws_hash_table_init
 * must be called before reusing the hash table.
 *
 * This method is idempotent.
 */
void aws_hash_table_clean_up(struct aws_hash_table *map)
{
  CBMC_CHECK_POINTER(map);
  struct hash_table_state* state = map->p_impl;
  assert(state->was_init);
  state->was_cleaned_up = true;
}

/**
 * Safely swaps two hash tables. Note that we swap the entirety of the hash
 * table, including which allocator is associated.
 *
 * Neither hash table is required to be initialized; if one or both is
 * uninitialized, then the uninitialized state is also swapped.
 */
void aws_hash_table_swap(struct aws_hash_table *AWS_RESTRICT a, struct aws_hash_table *AWS_RESTRICT b)
{
  CBMC_CHECK_POINTER(a);
  CBMC_CHECK_POINTER(b);
  struct aws_hash_table tmp = *a;
  *a = *b;
  *b = tmp;
}

/**
 * Moves the hash table in 'from' to 'to'. After this move, 'from' will
 * be identical to the state of the original 'to' hash table, and 'to'
 * will be in the same state as if it had been passed to aws_hash_table_clean_up
 * (that is, it will have no memory allocated, and it will be safe to
 * either discard it or call aws_hash_table_clean_up again).
 *
 * Note that 'to' will not be cleaned up. You should make sure that 'to'
 * is either uninitialized or cleaned up before moving a hashtable into
 * it.
 */
void aws_hash_table_move(struct aws_hash_table *AWS_RESTRICT to, struct aws_hash_table *AWS_RESTRICT from)
{
  struct hash_table_state* to_state = to->p_impl;
  assert(!to_state->was_init || to_state->was_cleaned_up);
  *to = *from;
}

/**
 * Returns the current number of entries in the table.
 */
size_t aws_hash_table_get_entry_count(const struct aws_hash_table *map)
{
  CBMC_CHECK_POINTER(map);
  struct hash_table_state* state = map->p_impl;
  return state->entry_count;
}

/**
 * Returns an iterator to be used for iterating through a hash table.
 * Iterator will already point to the first element of the table it finds,
 * which can be accessed as iter.element.
 *
 * This function cannot fail, but if there are no elements in the table,
 * the returned iterator will return true for aws_hash_iter_done(&iter).
 */
AWS_COMMON_API
struct aws_hash_iter aws_hash_iter_begin(const struct aws_hash_table *map)
{
  struct aws_hash_iter rval;
  rval.map = map;
  struct hash_table_state* state = map->p_impl;
  assert(state->was_init && !state->was_cleaned_up);
  rval.slot = 0;
  
  if(state->entry_count != 0){
    state->elem_maker(&rval.element, map);
  }
  return rval;
}

/* struct aws_hash_iter { */
/*     const struct aws_hash_table *map; */
/*     struct aws_hash_element element; */
/*     size_t slot; */
/*     size_t limit; */
/*     /\* */
/*      * Reserving extra fields for binary compatibility with future expansion of */
/*      * iterator in case hash table implementation changes. */
/*      *\/ */
/*     void *unused_0; */
/*     void *unused_1; */
/*     void *unused_2; */
/* }; */


/**
 * Returns true if iterator is done iterating through table, false otherwise.
 * If this is true, the iterator will not include an element of the table.
 */
AWS_COMMON_API
bool aws_hash_iter_done(const struct aws_hash_iter *iter)
{
  struct hash_table_state* state = iter->map->p_impl;
  return (iter->slot >= state->entry_count);
}

/**
 * Updates iterator so that it points to next element of hash table.
 *
 * This and the two previous functions are designed to be used together with
 * the following idiom:
 *
 * for (struct aws_hash_iter iter = aws_hash_iter_begin(&map);
 *      !aws_hash_iter_done(&iter); aws_hash_iter_next(&iter)) {
 *     key_type key = *(const key_type *)iter.element.key;
 *     value_type value = *(value_type *)iter.element.value;
 *     // etc.
 * }
 */
AWS_COMMON_API
void aws_hash_iter_next(struct aws_hash_iter *iter)
{
  struct hash_table_state* state = iter->map->p_impl;
  
  iter->slot++;
  if(!aws_hash_iter_done(iter)) {
    state->elem_maker(&iter->element, iter->map);
  } else {
    iter->element.key = nondet_voidp();
    iter->element.value = nondet_voidp();
  }
}

/**
 * Deletes the element currently pointed-to by the hash iterator.
 * After calling this method, the element member of the iterator
 * should not be accessed until the next call to aws_hash_iter_next.
 *
 * @param destroy_contents If true, the destructors for the key and value
 *  will be called.
 */
AWS_COMMON_API
void aws_hash_iter_delete(struct aws_hash_iter *iter, bool destroy_contents)
{
  assert(0);
}

/**
 * Attempts to locate an element at key.  If the element is found, a
 * pointer to the value is placed in *p_elem; if it is not found,
 * *pElem is set to NULL. Either way, AWS_OP_SUCCESS is returned.
 *
 * This method does not change the state of the hash table. Therefore, it
 * is safe to call _find from multiple threads on the same hash table,
 * provided no mutating operations happen in parallel.
 *
 * Calling code may update the value in the hash table by modifying **pElem
 * after a successful find. However, this pointer is not guaranteed to
 * remain usable after a subsequent call to _put, _delete, _clear, or
 * _clean_up.
 */

AWS_COMMON_API
int aws_hash_table_find(const struct aws_hash_table *map, const void *key, struct aws_hash_element **p_elem)
{
  assert(0);
  return nondet_int();
}

/**
 * Attempts to locate an element at key. If no such element was found,
 * creates a new element, with value initialized to NULL. In either case, a
 * pointer to the element is placed in *p_elem.
 *
 * If was_created is non-NULL, *was_created is set to 0 if an existing
 * element was found, or 1 is a new element was created.
 *
 * Returns AWS_OP_SUCCESS if an item was found or created.
 * Raises AWS_ERROR_OOM if hash table expansion was required and memory
 * allocation failed.
 */
AWS_COMMON_API
int aws_hash_table_create(
    struct aws_hash_table *map,
    const void *key,
    struct aws_hash_element **p_elem,
    int *was_created)
{
  struct hash_table_state* state = map->p_impl;

  bool already_exists;
  if(!already_exists){
    
  }
  assert(0);
  return nondet_int();
}

/**
 * Inserts a new element at key, with the given value. If another element
 * exists at that key, the old element will be overwritten; both old key and
 * value objects will be destroyed.
 *
 * If was_created is non-NULL, *was_created is set to 0 if an existing
 * element was found, or 1 is a new element was created.
 *
 * Returns AWS_OP_SUCCESS if an item was found or created.
 * Raises AWS_ERROR_OOM if hash table expansion was required and memory
 */
AWS_COMMON_API
int aws_hash_table_put(struct aws_hash_table *map, const void *key, void *value, int *was_created)
{
  assert(0);
  return nondet_int();
}

/**
 * Removes element at key. Always returns AWS_OP_SUCCESS.
 *
 * If pValue is non-NULL, the existing value (if any) is moved into
 * (*value) before removing from the table, and destroy_fn is _not_
 * invoked. If pValue is NULL, then (if the element existed) destroy_fn
 * will be invoked on the element being removed.
 *
 * If was_present is non-NULL, it is set to 0 if the element was
 * not present, or 1 if it was present (and is now removed).
 */
AWS_COMMON_API
int aws_hash_table_remove(
    struct aws_hash_table *map,
    const void *key,
    struct aws_hash_element *p_value,
    int *was_present)
{
  assert(0);
  return nondet_int();
}


/**
 * Iterates through every element in the map and invokes the callback on
 * that item. Iteration is performed in an arbitrary, implementation-defined
 * order, and is not guaranteed to be consistent across invocations.
 *
 * The callback may change the value associated with the key by overwriting
 * the value pointed-to by value. In this case, the on_element_removed
 * callback will not be invoked, unless the callback invokes
 * AWS_COMMON_HASH_TABLE_ITER_DELETE (in which case the on_element_removed
 * is given the updated value).
 *
 * The callback must return a bitmask of zero or more of the following values
 * ORed together:
 *
 * # AWS_COMMON_HASH_TABLE_ITER_CONTINUE - Continues iteration to the next
 *     element (if not set, iteration stops)
 * # AWS_COMMON_HASH_TABLE_ITER_DELETE   - Deletes the current value and
 *     continues iteration.  destroy_fn will NOT be invoked.
 *
 * Invoking any method which may change the contents of the hashtable
 * during iteration results in undefined behavior. However, you may safely
 * invoke non-mutating operations during an iteration.
 *
 * This operation is mutating only if AWS_COMMON_HASH_TABLE_ITER_DELETE
 * is returned at some point during iteration. Otherwise, it is non-mutating
 * and is safe to invoke in parallel with other non-mutating operations.
 */

AWS_COMMON_API
int aws_hash_table_foreach(
    struct aws_hash_table *map,
    int (*callback)(void *context, struct aws_hash_element *p_element),
    void *context)
{
  assert(0);
  return nondet_int();
}


/**
 * Compares two hash tables for equality. Both hash tables must have equivalent
 * key comparators; values will be compared using the comparator passed into this
 * function. The key hash function does not need to be equivalent between the
 * two hash tables.
 */
AWS_COMMON_API
bool aws_hash_table_eq(
    const struct aws_hash_table *a,
    const struct aws_hash_table *b,
    bool (*value_eq)(const void *a, const void *b))
{
  assert(0);
  return nondet_int();
}


/**
 * Removes every element from the hash map. destroy_fn will be called for
 * each element.
 */
AWS_COMMON_API
void aws_hash_table_clear(struct aws_hash_table *map)
{
  assert(0);
  return nondet_int();
}


/**
 * Convenience hash function for NULL-terminated C-strings
 */
AWS_COMMON_API
uint64_t aws_hash_c_string(const void *item);

/**
 * Convenience hash function for struct aws_strings.
 * Hash is same as used on the string bytes by aws_hash_c_string.
 */
AWS_COMMON_API
uint64_t aws_hash_string(const void *item);

/**
 * Convenience hash function for struct aws_byte_cursor.
 * Hash is same as used on the string bytes by aws_hash_c_string.
 */
AWS_COMMON_API
uint64_t aws_hash_byte_cursor_ptr(const void *item);

/**
 * Convenience hash function which hashes the pointer value directly,
 * without dereferencing.  This can be used in cases where pointer identity
 * is desired, or where a uintptr_t is encoded into a const void *.
 */
AWS_COMMON_API
uint64_t aws_hash_ptr(const void *item);

/**
 * Convenience eq function for NULL-terminated C-strings
 */
AWS_COMMON_API
bool aws_c_string_eq(const void *a, const void *b);

/**
 * Convenience eq function for struct aws_strings.
 */
AWS_COMMON_API
bool aws_string_eq(const void *a, const void *b);

/**
 * Convenience eq function for struct aws_byte_cursor.
 */
AWS_COMMON_API
bool aws_byte_cursor_ptr_eq(const void *a, const void *b);

/**
 * Equality function which compares pointer equality.
 */
AWS_COMMON_API
bool aws_ptr_eq(const void *a, const void *b);

AWS_EXTERN_C_END
