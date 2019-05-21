# Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#     http://aws.amazon.com/apache2.0/
#
# or in the "license" file accompanying this file. This file is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.

###########
#4: 25s
#8: 1m
#16: 5m45s
MAX_TABLE_SIZE ?= 2
DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE) 

#UNWINDSET += s_find_entry1.0:$(shell echo $$((1 + $(MAX_TABLE_SIZE))))
#UNWINDSET += memset_override_0_impl.0:$(shell echo $$(($$((3 * $$(( $(MAX_TABLE_SIZE) * 2 )) )) + 11)))
#UNWINDSET += s_expand_table.0:$(shell echo $$((1 + $(MAX_TABLE_SIZE))))
#UNWINDSET += s_emplace_item.0:$(shell echo $$((1 + $(MAX_TABLE_SIZE))))



CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(HELPERDIR)/stubs/memset_override_no_op.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c

ABSTRACTIONS +=  $(HELPERDIR)/stubs/s_expand_table_override.c

ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body __CPROVER_file_local_hash_table_c_s_expand_table

ENTRY = aws_hash_table_create_harness
###########

include ../Makefile.common
