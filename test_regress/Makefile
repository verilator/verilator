#*****************************************************************************
#
# DESCRIPTION: Verilator Example: Makefile for inside source directory
#
# This calls the object directory makefile.  That allows the objects to
# be placed in the "current directory" which simplifies the Makefile.
#
# Copyright 2003-2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
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

# Run tests in parallel.  Requires Parallel::Forker to be installed.
ifeq ($(CFG_WITH_LONGTESTS),yes)
 DRIVER_FLAGS ?= -j 0 --quiet --rerun
endif

.SUFFIXES:

######################################################################

SCENARIOS ?= --vlt --vltmt --dist
DRIVER_HASHSET ?=

.PHONY: test
test:
	$(PERL) driver.pl $(DRIVER_FLAGS) $(SCENARIOS) $(DRIVER_HASHSET)

######################################################################

vcs:
	$(PERL) driver.pl $(DRIVER_FLAGS) --vcs --stop

######################################################################

nc:
	$(PERL) driver.pl $(DRIVER_FLAGS) --nc --stop

######################################################################

vlt:
	$(PERL) driver.pl $(DRIVER_FLAGS) --vlt --stop

vltmt:
	$(PERL) driver.pl $(DRIVER_FLAGS) --vltmt --stop

######################################################################

random:
	$(PERL) driver.pl $(DRIVER_FLAGS) --optimize : --stop

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
	-rm -rf obj_* simv* simx* csrc cov_work INCA_libs *.log *.key logs vc_hdrs.h
	-rm -rf t/obj_*

distclean::
	-rm -rf snapshot

######################################################################
# Generated code snapshot and diff for tests

# Can be overridden for multiple snapshots
TEST_SNAP_DIR ?= snapshot

# Command to diff directories
TEST_DIFF_TOOL ?= $(if $(shell which icdiff), icdiff -N -r, diff -r)

TEST_SNAP_IGNORE := *.status *.log *.dat *.d *.o *.a *.so *stats*.txt *.html \
                    *.includecache *.out *.fst *.fst.vcd *.tree *.tree*.json \
                    *.dot *.csv *.xml *.hash *.cmake gmon.out.* CMakeFiles \
                    profile_exec.vcd t_pgo_threads

define TEST_SNAP_template
mkdir -p $(TEST_SNAP_DIR)
rm -rf $(TEST_SNAP_DIR)/obj_$(1)
cp -r obj_$(1) $(TEST_SNAP_DIR)/
find $(TEST_SNAP_DIR)/obj_$(1) \( $(TEST_SNAP_IGNORE:%=-name "%" -o) \
  -type f -executable \) -prune | xargs rm -r
endef

.PHONY: test-snap
test-snap:
	$(call TEST_SNAP_template,vlt)
	$(call TEST_SNAP_template,vltmt)
	$(call TEST_SNAP_template,dist)

.PHONY: impl-test-diff
impl-test-diff:
	$(TEST_DIFF_TOOL) $(TEST_SNAP_DIR)/obj_vlt   obj_vlt
	$(TEST_DIFF_TOOL) $(TEST_SNAP_DIR)/obj_vltmt obj_vltmt
	$(TEST_DIFF_TOOL) $(TEST_SNAP_DIR)/obj_dist  obj_dist

.PHONY: test-diff
test-diff:
	$(MAKE) impl-test-diff | grep -v "Only in obj_" | \
    $$(git config --default less --global --get core.pager)
