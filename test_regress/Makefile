#*****************************************************************************
#
# DESCRIPTION: Verilator Example: Makefile for inside source directory
#
# This calls the object directory makefile.  That allows the objects to
# be placed in the "current directory" which simplifies the Makefile.
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
#****************************************************************************/

default: test

# This must point to the root of the VERILATOR kit
VERILATOR_ROOT ?= $(shell pwd)/..
export VERILATOR_ROOT

# Pick up PERL and other variable settings
include $(VERILATOR_ROOT)/include/verilated.mk

######################################################################

ifneq ($(VCS_HOME),)
#Default to off, even with vcs; not all tests are ensured to be working
#PRODUCTS += --vcs
endif

ifneq ($(NC_ROOT),)
#Default to off, even with vcs; not all tests are ensured to be working
#PRODUCTS += --nc
endif

ifeq ($(CFG_WITH_LONGTESTS),yes)
  # Run tests in parallel.
  DRIVER_FLAGS ?= -j 0 --quiet --rerun
  # Save memory when test output directories are on a ramdisk, unless user set DRIVER_FLAGS
  ifeq ($(origin DRIVER_FLAGS),file)
    ifneq ($(VERILATOR_TESTS_OBJ_ROOT),)
      ifneq ($(filter tmpfs ramfs,$(shell stat -f -c %T $(VERILATOR_TESTS_OBJ_ROOT) 2>/dev/null)),)
        DRIVER_FLAGS += --driver-prune
      endif
    endif
  endif
endif

.SUFFIXES:

######################################################################

SCENARIOS ?= --vlt --vltmt --dist
DRIVER_HASHSET ?=

.PHONY: test
test:
	$(PYTHON3) driver.py $(DRIVER_FLAGS) $(SCENARIOS) $(DRIVER_HASHSET)

######################################################################

vlt:
	$(PYTHON3) driver.py $(DRIVER_FLAGS) --vlt --stop

vltmt:
	$(PYTHON3) driver.py $(DRIVER_FLAGS) --vltmt --stop

######################################################################

random:
	$(PYTHON3) driver.py $(DRIVER_FLAGS) --optimize : --stop

random_forever:
	while ( VERILATOR_NO_DEBUG=1 CPPFLAGS_ADD=-Wno-error $(MAKE) random ) ; do \
		echo ; \
	done

#######################################################################
# Informational - used by some tests

print-cxx-version:
	$(CXX) --version

######################################################################
maintainer-copy::
clean mostlyclean distclean maintainer-clean::
	-rm -rf obj_*/ obj_* simv* simx* csrc cov_work INCA_libs *.log *.key logs vc_hdrs.h
	-rm -rf t/obj_* t/__pycache__

distclean::
	-rm -rf snapshot

######################################################################
# Generated code snapshot and diff for tests

# Can be overridden for multiple snapshots
TEST_SNAP_DIR ?= snapshot

.PHONY: test-snap
test-snap:
	$(PYTHON3) test_diff.py snap --snap-dir $(TEST_SNAP_DIR)

.PHONY: test-diff
test-diff:
	$(PYTHON3) test_diff.py diff --snap-dir $(TEST_SNAP_DIR) \
	| $$(git config --default less --global --get core.pager)
