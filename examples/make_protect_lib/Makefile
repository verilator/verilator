######################################################################
#
# DESCRIPTION: Verilator Example: --protect-lib Makefile
#
# This calls the object directory makefiles.  That allows the objects to
# be placed in the "current directory" which simplifies the Makefile.
#
# Copyright 2019 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
######################################################################
# Check for sanity to avoid later confusion

ifneq ($(words $(CURDIR)),1)
 $(error Unsupported: GNU Make cannot build in directories containing spaces, build elsewhere: '$(CURDIR)')
endif

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

VERILATOR_FLAGS =
# Generate C++
VERILATOR_FLAGS += -cc
# Optimize
VERILATOR_FLAGS += -Os -x-assign 0
# Warn abount lint issues; may not want this on less solid designs
VERILATOR_FLAGS += -Wall
# Make waveforms
TOP_VERILATOR_FLAGS = $(VERILATOR_FLAGS) --trace

######################################################################
default: run

run:
	@echo
	@echo "-- Verilator --protect-lib example -_--------------------------"

	@echo
	@echo "-- VERILATE secret module -------------------------------------"
	@echo " --protect-lib will produce both a static and shared library"
	@echo " In this example the static library is used, but some"
	@echo " simulators may require the shared library."
	@echo "---------------------------------------------------------------"
	$(VERILATOR) $(VERILATOR_FLAGS) --protect-lib verilated_secret -Mdir obj_dir_secret/ secret_impl.v

	@echo
	@echo "-- COMPILE protected library ----------------------------------"
	@echo " This builds verilated_secret.sv, libverilated_secret.a and"
	@echo " libverilated_secret.so which can be distributed apart from"
	@echo " the source"
	@echo "---------------------------------------------------------------"
	$(MAKE) -j 4 -C obj_dir_secret -f Vsecret_impl.mk

	@echo
	@echo "-- VERILATE top module ----------------------------------------"
	@echo " Use the SystemVerilog wrapper (verilated_secret.sv) and the"
	@echo " library (libverilated_secret.a) generated from the previous"
	@echo " step"
	@echo "---------------------------------------------------------------"
	$(VERILATOR) $(TOP_VERILATOR_FLAGS) --exe -LDFLAGS '-L../obj_dir_secret -lverilated_secret -static' top.v obj_dir_secret/verilated_secret.sv sim_main.cpp

	@echo
	@echo "-- COMPILE entire design --------------------------------------"
	$(MAKE) -j 4 -C obj_dir -f Vtop.mk

	@echo
	@echo "-- RUN --------------------------------------------------------"
	@mkdir -p logs
	obj_dir/Vtop +trace

	@echo
	@echo "-- DONE -------------------------------------------------------"
	@echo "To see waveforms, open logs/vlt_dump.vcd in a waveform viewer"
	@echo


######################################################################
# Other targets

show-config:
	$(VERILATOR) -V

maintainer-copy::
clean mostlyclean distclean maintainer-clean::
	-rm -rf obj_dir* logs *.log core
