#*****************************************************************************
# DESCRIPTION: Verilator documentation: Makefile pre-configure version
#
# This file is part of Verilator.
#
# Code available from: http://www.veripool.org/verilator
#
#*****************************************************************************
#
# Copyright 2003-2019 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
# Verilator is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
#****************************************************************************/
#
# This file is intended only to be called from the top-level Verilator Makefile.

#### Start of system configuration section. ####

DOXYGEN = doxygen

#### End of system configuration section. ####
######################################################################

.SUFFIXES:

default:
	@echo "error: make not supported here, run 'make docs' from Verilator top-level"

clean mostlyclean distclean maintainer-clean::
	rm -f $(SCRIPTS) *.tmp
	rm -f *.aux *.cp *.cps *.dvi *.fn *.fns *.ky *.kys *.log
	rm -f *.pg *.pgs *.toc *.tp *.tps *.vr *.vrs *.idx
	rm -f *.ev *.evs *.ov *.ovs *.cv *.cvs *.ma *.mas
	rm -f *.tex

distclean maintainer-clean::
	rm -f *.info* *.1 $(INFOS)
	rm -f Makefile

.PHONY: doxygen

doxygen:
	$(DOXYGEN) doxygen.config
