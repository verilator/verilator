######################################################################
#
# DESCRIPTION: Verilator Example: XML tests
#
# Copyright 2003-2020 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
######################################################################

# This makefile is not intended to be useful as an example itself,
# it is just to run the small example scripts in this directory.

# If $VERILATOR_ROOT isn't in the environment, we assume it is part of a
# package install, and verilator is in your path. Otherwise find the
# binary relative to $VERILATOR_ROOT (such as when inside the git sources).
ifeq ($(VERILATOR_ROOT),)
VERILATOR = verilator
else
export VERILATOR_ROOT
VERILATOR = $(VERILATOR_ROOT)/bin/verilator
endif

DOT = dot
PYTHON = python3

PYTHON_VERSION := $(shell ${PYTHON} --version 2>&1)
PYTHON_VERSION_FULL := $(wordlist 2,4,$(subst ., ,${PYTHON_VERSION}))
PYTHON_VERSION_MAJOR := $(word 1,${PYTHON_VERSION_FULL})
PYTHON_VERSION_MINOR := $(word 2,${PYTHON_VERSION_FULL})
PYTHON_GE_3_5 := $(shell [ ${PYTHON_VERSION_MAJOR} -eq 3 -a ${PYTHON_VERSION_MINOR} -ge 5 ] && echo true)

ifeq (${PYTHON_GE_3_5},true)
default: test
else
default: python_message
endif

python_message:
	@echo "Found Python version ${PYTHON_VERSION}, but require >= 3.5"

test: \
	test-vl_file_copy \
	test-vl_hier_graph \

test-vl_file_copy:
	@echo "-- vl_file_copy example"
	$(PYTHON) vl_file_copy -odir copied top.v
	@cmp copied/top.v top.v
	@cmp copied/sub.v sub.v

test-vl_hier_graph:
	@echo "-- vl_hier_graph example"
	$(PYTHON) vl_hier_graph -o graph.dot top.v
	@echo "Manually run: " $(DOT) -Tpdf -o graph.pdf graph.dot

######################################################################

maintainer-copy::
clean mostlyclean distclean maintainer-clean::
	-rm -rf obj_dir *.log *.csv *.dmp *.dot *.vpd *.pdf core copied
