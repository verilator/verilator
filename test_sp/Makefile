#*****************************************************************************
#
# DESCRIPTION: Verilator Example: Makefile for inside source directory
#
# This calls the object directory makefile.  That allows the objects to
# be placed in the "current directory" which simplifies the Makefile.
#
# Copyright 2003-2012 by Wilson Snyder. This program is free software; you can
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

DEBUG_ON = --debug --trace-dups

######################################################################
ifneq ($(SYSTEMPERL),)
test_default:  precopy prep        preproc compile     run coverage
test_debug:    precopy prep_dbg    preproc compile_dbg run coverage
test_nopublic: precopy prep_dbg_np preproc compile_dbg run coverage
else
test_default:  nosp
test_debug:    nosp
test_nopublic: nosp
endif

V_FLAGS = -f $(VERILATOR_ROOT)/test_v/input.vc

# Note the --public --output-split-cfunc is here for testing only,
# Avoid using these settings in real application Makefiles!
VERILATOR_FLAGS = --public --output-split-cfuncs 1000 --output-split 1000 \
	--sp --coverage --stats --trace $(V_FLAGS) top.v

precopy: obj_dir obj_dir/sc_main.cpp
obj_dir/sc_main.cpp: ../test_sc/sc_main.cpp
	mkdir -p obj_dir
	cp $^ $@

prep:
	$(PERL) $(VERILATOR_ROOT)/bin/verilator             $(VERILATOR_FLAGS)
prep_dbg:
	$(PERL) $(VERILATOR_ROOT)/bin/verilator $(DEBUG_ON) $(VERILATOR_FLAGS)
prep_dbg_np:
	$(PERL) $(VERILATOR_ROOT)/bin/verilator $(DEBUG_ON) $(VERILATOR_FLAGS) --nopublic

preproc:
	cd obj_dir ; $(MAKE) -j 1 -f ../Makefile_obj preproc

compile:
	cd obj_dir ; $(MAKE)        -j 3 -f ../Makefile_obj

compile_dbg:
	cd obj_dir ; $(MAKE) OPT=-g -j 3 -f ../Makefile_obj

run:
	obj_dir/simx

coverage:
	vcoverage $(V_FLAGS)

######################################################################

obj_dir:
	mkdir $@

nosp:
	@echo
	@echo %Skip: SYSTEMPERL not in environment
	@echo

######################################################################

maintainer-copy::
clean mostlyclean distclean maintainer-clean::
	-rm -rf obj_dir *.log *.dmp *.vpd *.vcd core logs

