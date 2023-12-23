# DESCRIPTION: Verilator: Makefile for Verilog Test module
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2023 by Shupei Fan.
# SPDX-License-Identifier: CC0-1.0

include Vt_flag_lib_dpi.mk

t_flag_lib_dpi_test: libVt_flag_lib_dpi.a libverilated.a
	$(LINK) $(LDFLAGS) $^ $(LDLIBS) -o $@
