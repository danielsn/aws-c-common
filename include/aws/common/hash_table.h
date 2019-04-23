#ifndef AWS_COMMON_HASH_TABLE_H
#define AWS_COMMON_HASH_TABLE_H

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

#include <stddef.h>

#define AWS_COMMON_HASH_TABLE_ITER_CONTINUE (1 << 0)
#define AWS_COMMON_HASH_TABLE_ITER_DELETE (1 << 1)

/**
 * Hash table data structure. This module provides an automatically resizing
 * hash table implementation for general purpose use. The hash table stores a
 * mapping between void * keys and values; it is expected that in most cases,
 * these will point to a structure elsewhere in the heap, instead of inlining a
 * key or value into the hash table element itself.
 *
 * Currently, this hash table implements a variant of robin hood hashing, but
 * we do not guarantee that this won't change in the future.
 *
 * Associated with each hash function are four callbacks:
 *
 *   hash_fn - A hash function from the keys to a uint64_t. It is critical that
 *      the hash function for a key does not change while the key is in the hash
 *      table; violating this results in undefined behavior. Collisions are
 *      tolerated, though naturally with reduced performance.
 *
 *   equals_fn - An equality comparison function. This function must be
 *      reflexive and consistent with hash_fn.
 *
 *   destroy_key_fn, destroy_value_fn - Optional callbacks invoked when the
 *      table is cleared or cleaned up and at the caller's option when an element
 *      is removed from the table. Either or both may be set to NULL, which
 *      has the same effect as a no-op destroy function.
 *
 * This datastructure can be safely moved between threads, subject to the
 * requirements of the underlying allocator. It is also safe to invoke
 * non-mutating operations on the hash table from multiple threads. A suitable
 * memory barrier must be used when transitioning from single-threaded mutating
 * usage to multithreaded usage.
 */
struct hash_table_state; /* Opaque pointer */
struct aws_hash_table {
    struct hash_table_state *p_impl;
};

/**
 * Represents an element in the hash table. Various operations on the hash
 * table may provide pointers to elements stored within the hash table;
 * generally, calling code may alter value, but must not alter key (or any
 * information used to compute key's hash code).
 *
 * Pointers to elements within the hash are invalidated whenever an operation
 * which may change the number of elements in the hash is invoked (i.e. put,
 * delete, clear, and clean_up), regardless of whether the number of elements
 * actually changes.
 */
struct aws_hash_element {
    const void *key;
    void *value;
};

enum aws_hash_iter_status {
    AWS_HASH_ITER_STATUS_DONE,
    AWS_HASH_ITER_STATUS_DELETE_CALLED,
    AWS_HASH_ITER_STATUS_READY_FOR_USE,
};

/* aws_hash_iter has reserved fields of type void*. If this assertion below is true, we can
 * use intptr_t in these fields without issue.
 */
AWS_STATIC_ASSERT(sizeof(intptr_t) == sizeof(void *));

struct aws_hash_iter {
    const struct aws_hash_table *map;
    struct aws_hash_element element;
    size_t slot;
    size_t limit;
    /* Holds an enum aws_hash_iter_status */
    intptr_t status;
    /*
     * Reserving extra fields for binary compatibility with future expansion of
     * iterator in case hash table implementation changes.
     */
    void *unused_0;
    void *unused_1;
};

/**
 * Prototype for a key hashing function pointer.
 */
typedef uint64_t(aws_hash_fn)(const void *key);

/**
 * Prototype for a hash table equality check function pointer.
 *
 * This type is usually used for a function that compares two hash table
 * keys, but note that the same type is used for a function that compares
 * two hash table values in aws_hash_table_eq.
 *
 * Equality functions used in a hash table must be reflexive (i.e., a == b if
 * and only if b == a), and must be consistent with the hash function in use.
 */
typedef bool(aws_hash_callback_eq_fn)(const void *a, const void *b);

/**
 * Prototype for a hash table key or value destructor function pointer.
 *
 * This function is used to destroy elements in the hash table when the
 * table is cleared or cleaned up.
 *
 * Note that functions which remove individual elements from the hash
 * table provide options of whether or not to invoke the destructors
 * on the key and value of a removed element.
 */
typedef void(aws_hash_callback_destroy_fn)(void *key_or_value);

AWS_EXTERN_C_BEGIN

/**
 * Initializes a hash map with initial capacity for 'size' elements
 * without resizing. Uses hash_fn to compute the hash of each element.
 * equals_fn to compute equality of two keys.  Whenever an element is
 * removed without being returned, destroy_key_fn is run on the pointer
 * to the key and destroy_value_fn is run on the pointer to the value.
 * Either or both may be NULL if a callback is not desired in this case.
 */
AWS_COMMON_API
int aws_hash_table_init(
    struct aws_hash_table *map,
    struct aws_allocator *alloc,
    size_t size,
    aws_hash_fn *hash_fn,
    aws_hash_callback_eq_fn *equals_fn,
    aws_hash_callback_destroy_fn *destroy_key_fn,
    aws_hash_callback_destroy_fn *destroy_value_fn);

/**
 * Deletes every element from map and frees all associated memory.
 * destroy_fn will be called for each element.  aws_hash_table_init
 * must be called before reusing the hash table.
 *
 * This method is idempotent.
 */
AWS_COMMON_API
void aws_hash_table_clean_up(struct aws_hash_table *map);

/**
 * Safely swaps two hash tables. Note that we swap the entirety of the hash
 * table, including which allocator is associated.
 *
 * Neither hash table is required to be initialized; if one or both is
 * uninitialized, then the uninitialized state is also swapped.
 */
AWS_COMMON_API
void aws_hash_table_swap(struct aws_hash_table *AWS_RESTRICT a, struct aws_hash_table *AWS_RESTRICT b);

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
AWS_COMMON_API
void aws_hash_table_move(struct aws_hash_table *AWS_RESTRICT to, struct aws_hash_table *AWS_RESTRICT from);

/**
 * Returns the current number of entries in the table.
 */
AWS_COMMON_API
size_t aws_hash_table_get_entry_count(const struct aws_hash_table *map);

/**
 * Returns an iterator to be used for iterating through a hash table.
 * Iterator will already point to the first element of the table it finds,
 * which can be accessed as iter.element.
 *
 * This function cannot fail, but if there are no elements in the table,
 * the returned iterator will return true for aws_hash_iter_done(&iter).
 */
AWS_COMMON_API
struct aws_hash_iter aws_hash_iter_begin(const struct aws_hash_table *map);

/**
 * Returns true if iterator is done iterating through table, false otherwise.
 * If this is true, the iterator will not include an element of the table.
 */
AWS_COMMON_API
bool aws_hash_iter_done(const struct aws_hash_iter *iter);

/**
 * Updates iterator so that it points to next element of hash table.
 *
 * This and the two previous functions are designed to be used together with
 * the following idiom:
 *
 * for (struct aws_hash_iter iter = aws_hash_iter_begin(&map);
 *      !aws_hash_iter_done(&iter); aws_hash_iter_next(&iter)) {
 *     const key_type key = *(const key_type *)iter.element.key;
 *     value_type value = *(value_type *)iter.element.value;
 *     // etc.
 * }
 *
 * Note that calling this on an iter which is "done" is idempotent:
 * i.e. it will return another iter which is "done".
 */
AWS_COMMON_API
void aws_hash_iter_next(struct aws_hash_iter *iter);

/**
 * Deletes the element currently pointed-to by the hash iterator.
 * After calling this method, the element member of the iterator
 * should not be accessed until the next call to aws_hash_iter_next.
 *
 * @param destroy_contents If true, the destructors for the key and value
 *  will be called.
 */
AWS_COMMON_API
void aws_hash_iter_delete(struct aws_hash_iter *iter, bool destroy_contents);

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
int aws_hash_table_find(const struct aws_hash_table *map, const void *key, struct aws_hash_element **p_elem);

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
    int *was_created);

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
int aws_hash_table_put(struct aws_hash_table *map, const void *key, void *value, int *was_created);

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
    int *was_present);

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
    void *context);

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
    aws_hash_callback_eq_fn *value_eq);

/**
 * Removes every element from the hash map. destroy_fn will be called for
 * each element.
 */
AWS_COMMON_API
void aws_hash_table_clear(struct aws_hash_table *map);

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
 * Convenience eq callback for NULL-terminated C-strings
 */
AWS_COMMON_API
bool aws_hash_callback_c_str_eq(const void *a, const void *b);

/**
 * Convenience eq callback for AWS strings
 */
AWS_COMMON_API
bool aws_hash_callback_string_eq(const void *a, const void *b);

/**
 * Convenience destroy callback for AWS strings
 */
AWS_COMMON_API
void aws_hash_callback_string_destroy(void *a);

/**
 * Equality function which compares pointer equality.
 */
AWS_COMMON_API
bool aws_ptr_eq(const void *a, const void *b);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_HASH_TABLE_H */
