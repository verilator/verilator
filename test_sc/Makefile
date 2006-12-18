# $Id$ */
#*****************************************************************************
#
# DESCRIPTION: Verilator Example: Makefile for inside source directory
#
# This calls the object directory makefile.  That allows the objects to
# be placed in the "current directory" which simplifies the Makefile.
#
# Copyright 2003-2006 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.
#
#****************************************************************************/

# This must point to the root of the VERILATOR kit
VERILATOR_ROOT := $(shell pwd)/..
export VERILATOR_ROOT

PERL = perl

DEBUG_ON = --debug

######################################################################
default:  precopy prep        preproc compile run
debug:    precopy prep_dbg    preproc compile run
nopublic: precopy prep_dbg_np preproc compile run

V_FLAGS = -f $(VERILATOR_ROOT)/test_v/input.vc
VERILATOR_FLAGS = --sc $(V_FLAGS) top.v

precopy: obj_dir obj_dir/sc_main.cpp
obj_dir/sc_main.cpp: ../test_sp/sc_main.cpp
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
	cd obj_dir ; $(MAKE) -j 3 -f ../Makefile_obj

run:	
	obj_dir/simx

######################################################################

obj_dir:
	mkdir $@

######################################################################

maintainer-copy::
clean mostlyclean distclean maintainer-clean::
	-rm -rf obj_dir *.log *.dmp *.vpd *.vcd core

