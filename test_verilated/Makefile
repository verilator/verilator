#*****************************************************************************
#
# DESCRIPTION: Verilator Example: Makefile for inside source directory
#
# This calls the object directory makefile.  That allows the objects to
# be placed in the "current directory" which simplifies the Makefile.
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
#****************************************************************************/

default: test

# This must point to the root of the VERILATOR kit
VERILATOR_ROOT := $(shell pwd)/..
export VERILATOR_ROOT

VERILATOR_NCVERILOG ?= ncverilog
VERILATOR_VCS ?= vcs

# Pick up PERL and other variable settings
include $(VERILATOR_ROOT)/include/verilated.mk

VERILATOR_SW +=
ifeq ($(VERILATOR_NO_DEBUG),)
  VERILATOR_SW += --debug --no-dump-tree
endif

PERL_PACKAGES_OK := $(shell $(PERL) -e 'eval "use Bit::Vector; print 1;";')

######################################################################

default: test

ifneq ($(PERL_PACKAGES_OK),1)
test::  nopackages
else
 ifneq ($(VCS_HOME),)
test::	vcs
 else
test::	novcs
 endif

 ifneq ($(NC_ROOT),)
test::	nc
 else
test::	nonc
 endif

test::	vlt
endif

vgen.v: ./vgen.pl
	$(PERL) vgen.pl $(VGEN_FLAGS)

#	We ulimit cpu time, as some cases make gcc 3.3.4 hang
random:
	-rm -rf obj_dir/Vgen* obj_dir/simx
	$(PERL) vgen.pl --seed=0 --numops=1000 --depth=4 --raise=4
	VERILATOR_NO_DEBUG=1 CPPFLAGS_ADD=-Wno-error VCS_HOME= NC_ROOT= bash -c "ulimit -t 120; $(MAKE) test"
#	$(MAKE) nc

random_forever:
	while ( $(MAKE) random ) ; do \
		echo ; \
	done

######################################################################

nopackages:
	@echo "No perl Bit::Vector package installed."
	@echo "Not running regression test."

novcs:
	@echo "No VCS simulator installed."
	@echo "Not running VCS regression test."

vcs:	vcs_passed.log

simv:	vgen.v sim_main.v
	vcs +cli -I +define+vcs+1 +v2k -q vgen.v sim_main.v

vcs_passed.log	: simv
	-rm -f vcs_passed.log
	./simv -l sim.log
	grep -q Finished sim.log && grep Finished sim.log > vcs_passed.log

######################################################################

nonc:
	@echo "No NC-Verilog simulator installed."
	@echo "Not running NC-Verilog regression test."

nc:	nc_passed.log

nc_passed.log:	vgen.v sim_main.v
	$(VERILATOR_NCVERILOG) +licqueue +define+ncverilog=1 -q vgen.v sim_main.v
	-rm -f nc_passed.log
	grep -q Finished ncverilog.log && grep Finished ncverilog.log > nc_passed.log

######################################################################

vlt:	prep compile vlt_passed.log

prep: 	vgen.v $(VERILATOR_ROOT)/bin/verilator
	$(PERL) $(VERILATOR_ROOT)/bin/verilator $(VERILATOR_SW) --cc vgen.v

compile:
	cd obj_dir ; $(MAKE) -j 3 -f ../Makefile_obj

vlt_passed.log vlt_run: prep compile
	-rm -f vlt_passed.log sim.log
	obj_dir/simx | tee sim.log
	grep -q Finished sim.log && grep Finished sim.log > vlt_passed.log

######################################################################
maintainer-copy::
clean mostlyclean distclean maintainer-clean::
	-rm -rf obj_dir *.log *.dmp *.vpd simv* *.key vgen.v csrc INCA_libs

