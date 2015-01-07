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

default: show_config test_default

# This must point to the root of the VERILATOR kit
VERILATOR_ROOT := $(shell pwd)/..
export VERILATOR_ROOT

# Pick up PERL and other variable settings
include $(VERILATOR_ROOT)/include/verilated.mk

DEBUG_QUIET = --debug --debugi 0 --gdbbt --no-dump-tree
DEBUG_ON = --debug --trace-dups --gdbbt
#DEBUG = $(DEBUG_ON)
VALGRIND_ON = $(DEBUG_ON) --gdb "valgrind -v --leak-check=yes"

######################################################################
test_default:   prep     compile run
test_debug:     prep_dbg compile run
test_valgrind:  prep_vg  compile run

VERILATOR_FLAGS = --cc -f $(VERILATOR_ROOT)/test_v/input.vc top.v
VERILATOR_FLAGS += --trace

#show_config: Is the very first time we've executed Verilator after building
#so we make sure to run with --gdbbt, so if it dumps we'll get a trace.
show_config:
	$(PERL) $(VERILATOR_ROOT)/bin/verilator $(DEBUG_QUIET) -V

#prep: Is the very first time we're running a Verilation
#so we make sure to run with --gdbbt, so if it dumps we'll get a trace.
prep:
	$(PERL) $(VERILATOR_ROOT)/bin/verilator $(DEBUG_QUIET) $(VERILATOR_FLAGS)
prep_dbg:
	$(PERL) $(VERILATOR_ROOT)/bin/verilator $(DEBUG_ON)    $(VERILATOR_FLAGS)
prep_vg:
	$(PERL) $(VERILATOR_ROOT)/bin/verilator $(VALGRIND_ON) $(VERILATOR_FLAGS)

compile:
	cd obj_dir ; $(MAKE) -j 3 -f ../Makefile_obj

run:
	obj_dir/simx

######################################################################

obj_dir:
	mkdir $@

######################################################################

maintainer-copy::
clean mostlyclean distclean maintainer-clean::
	-rm -rf obj_dir *.log *.dmp *.vpd core
