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
include ../Makefile.aws_array_list
include ../Makefile.aws_priority_queue_sift

###########
#
# Runtime:
# - 300s for MAX_PRIORITY_QUEUE_ITEMS=3 items
# 

# Note:
# In order to reach full coverage we need to unwind the harness loop
# as many times as the number of queue items, and the sift down loop
# log(NUMBER_PRIO_QUEUE_ITEMS) times.
UNWINDSET += __CPROVER_file_local_priority_queue_c_s_sift_down.0:$(MAX_HEAP_HEIGHT)
UNWINDSET += __CPROVER_file_local_priority_queue_c_s_sift_up.0:$(MAX_HEAP_HEIGHT)
UNWINDSET += aws_priority_queue_s_sift_either_harness.0:$(shell echo $$((1 + $(MAX_PRIORITY_QUEUE_ITEMS))))
UNWINDSET += aws_priority_queue_backpointers_valid_deep.0:$(shell echo $$((1 + $(MAX_PRIORITY_QUEUE_ITEMS))))

CBMCFLAGS += 

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(HELPERDIR)/stubs/memcpy_override_havoc.c
DEPENDENCIES += $(SRCDIR)/source/array_list.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/priority_queue.c

ABSTRACTIONS +=  $(HELPERDIR)/stubs/s_swap_override_no_op.c

ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body __CPROVER_file_local_priority_queue_c_s_swap

ENTRY = aws_priority_queue_s_sift_either_harness
###########

include ../Makefile.common

