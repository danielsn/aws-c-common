#include <aws/common/hash_table.h>
#include <aws/common/math.h>
#include <aws/common/private/hash_table_impl.h>
#include <aws/common/string.h>

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>


int s_expand_table(struct aws_hash_table *map) {
    struct hash_table_state *old_state = map->p_impl;
    struct hash_table_state template = *old_state;

    s_update_template_size(&template, template.size * 2);

    /* Don't use s_alloc_state because that will call calloc
     * and we want non-det values for the entries
     */
    size_t required_bytes;
    if (hash_table_state_required_bytes(template.size, &required_bytes)) {
        return NULL;
    }

    /* An empty slot has hashcode 0. So this marks all slots as empty */
    struct hash_table_state *new_state = aws_mem_alloc(template.alloc, required_bytes);

    if (new_state == NULL) {
        return AWS_OP_ERR;
    }

    *new_state = template;
    
    map->p_impl = new_state;
    aws_mem_release(new_state->alloc, old_state);
    __CPROVER_assume(aws_hash_table_is_valid(map));
    size_t empty_slot_idx;
    __CPROVER_assume(aws_hash_table_has_an_empty_slot(&map, &empty_slot_idx));
    return AWS_OP_SUCCESS;
}

