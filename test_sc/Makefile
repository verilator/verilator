#*****************************************************************************
#
# DESCRIPTION: Verilator Example: Makefile for inside source directory
#
# This calls the object directory makefile.  That allows the objects to
# be placed in the "current directory" which simplifies the Makefile.
#
# Copyright 2003-2015 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
#****************************************************************************/

default: test_default

# This must point to the root of the VERILATOR kit
VERILATOR_ROOT := $(shell pwd)/..
export VERILATOR_ROOT

# Pick up PERL and other variable settings
include $(VERILATOR_ROOT)/include/verilated.mk

DEBUG_ON = --debug
SYSTEMC_TESTING ?= $(SYSTEMC)$(SYSTEMC_INCLUDE)

######################################################################
ifneq ($(SYSTEMC_TESTING),)
test_default:  precopy prep        compile run
test_debug:    precopy prep_dbg    compile run
else
test_default:  nosc
test_debug:    nosc
endif

V_FLAGS = -f $(VERILATOR_ROOT)/test_v/input.vc
VERILATOR_FLAGS = --sc $(V_FLAGS) top.v
VERILATOR_FLAGS += --trace

precopy:

prep:
	$(PERL) $(VERILATOR_ROOT)/bin/verilator             $(VERILATOR_FLAGS)
prep_dbg:
	$(PERL) $(VERILATOR_ROOT)/bin/verilator $(DEBUG_ON) $(VERILATOR_FLAGS)

compile:
	cd obj_dir ; $(MAKE) -j 3 -f ../Makefile_obj

run:
	obj_dir/simx

######################################################################

obj_dir:
	mkdir $@

nosc:
	@echo
	@echo %Skip: SYSTEMC_INCLUDE not in environment
	@echo

######################################################################

maintainer-copy::
clean mostlyclean distclean maintainer-clean::
	-rm -rf obj_dir *.log *.dmp *.vpd *.vcd core

