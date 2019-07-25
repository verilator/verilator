######################################################################
#
# DESCRIPTION: Verilator Python make example usage
#
# This file shows usage of the Python support using make.
#
# Copyright 2003-2019 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
######################################################################

######################################################################
# Set up variables

# If $VERILATOR_ROOT isn't in the environment, we assume it is part of a
# package install, and verilator is in your path. Otherwise find the
# binary relative to $VERILATOR_ROOT (such as when inside the git sources).

ifeq ($(VERILATOR_ROOT),)
VERILATOR = verilator
else
export VERILATOR_ROOT
VERILATOR = $(VERILATOR_ROOT)/bin/verilator
endif
######################################################################

# Check if pybind11 is available
ifeq (${PYBIND11_ROOT},)
TARGET := nopybind11
else
TARGET := run
endif

default: $(TARGET)

run:
	@echo "-- Verilator Python example using nake"
	@echo "PYBIND11_ROOT is $(PYBIND11_ROOT)"

	@echo "-- VERILATE ----------------"
	$(VERILATOR) -cc --python --make gmake top.v

	@echo "-- COMPILE -----------------"
	$(MAKE) -j 4 -C obj_dir -f Vtop.mk

	@echo "-- RUN ---------------------"
	python3 sim_main.py

	@echo "-- DONE --------------------"

######################################################################

maintainer-copy::
clean mostlyclean distclean maintainer-clean::
	-rm -rf obj_dir *.log *.dmp *.vpd core

nopybind11:
	@echo
	@echo "%Skip: Python example disabled because the PYBIND11_ROOT environment variable was not set."
	@echo "%This example can be enabled by install pybind11 and setting the PYBIND11_ROOT environment variable."
	@echo
