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

default: test

# This must point to the root of the VERILATOR kit
VERILATOR_ROOT := $(shell pwd)/..
export VERILATOR_ROOT

# Pick up PERL and other variable settings
include $(VERILATOR_ROOT)/include/verilated.mk

######################################################################

ifneq ($(VCS_HOME),)
#Default to off, even with vcs; not all tests are insured to be working
#PRODUCTS += --vcs
endif

ifneq ($(NC_ROOT),)
#Default to off, even with vcs; not all tests are insured to be working
#PRODUCTS += --nc
endif

PRODUCTS += --vlt

# Run tests in parallel.  Requires Parallel::Forker to be installed.
ifeq ($(CFG_WITH_LONGTESTS),yes)
 DRIVER_FLAGS += -j 0
endif

######################################################################

.PHONY: test
test:
	$(PERL) driver.pl $(DRIVER_FLAGS) $(PRODUCTS)

######################################################################

vcs:
	$(PERL) driver.pl $(DRIVER_FLAGS) --vcs --stop

######################################################################

nc:
	$(PERL) driver.pl $(DRIVER_FLAGS) --nc --stop

######################################################################

vlt:
	$(PERL) driver.pl $(DRIVER_FLAGS) --vlt --stop

######################################################################

random:
	$(PERL) driver.pl $(DRIVER_FLAGS) --optimize : --stop

random_forever:
	while ( VERILATOR_NO_DEBUG=1 CPPFLAGS_ADD=-Wno-error $(MAKE) random ) ; do \
		echo ; \
	done

######################################################################
maintainer-copy::
clean mostlyclean distclean maintainer-clean::
	-rm -rf obj_dir simv* simx* csrc cov_work INCA_libs *.log *.key logs vc_hdrs.h
