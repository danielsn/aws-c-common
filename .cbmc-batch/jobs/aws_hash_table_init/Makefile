# Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
MAX_TABLE_SIZE ?= 2
DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE) 

#UNWINDSET += memcpy_using_uint64_impl.0:14
#UNWINDSET += memset_using_uint64_impl.0:14 #A hash entry is 24 bytes, and there are 4 of them to start
UNWINDSET += memcpy_using_uint64_impl.0:9
UNWINDSET += memset_using_uint64_impl.0:9 #A hash entry is 24 bytes, and there are 4 of them to start
UNWINDSET += s_update_template_size.0:17

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/stubs/memcmp_override.c
DEPENDENCIES += $(HELPERDIR)/stubs/memcpy_using_uint64.c
DEPENDENCIES += $(HELPERDIR)/stubs/memset_using_uint64.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/error.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c

ENTRY = aws_hash_table_init_harness
###########

include ../Makefile.common
