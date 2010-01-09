#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 verilator_flags2 => [qw(--lint-only)],
	 verilator_make_gcc => 0,
	 make_top_shell => 0,
	 make_main => 0,
	 fails=>$Self->{vlt},
	 expect=>
'%Warning-LITENDIAN: t/t_metacmt_onoff.v:\d+: Little bit endian vector: MSB < LSB of bit range: 0:1
%Warning-LITENDIAN: Use "/\* verilator lint_off LITENDIAN \*/" and lint_on around source to disable this message.
%Warning-LITENDIAN: t/t_metacmt_onoff.v:\d+: Little bit endian vector: MSB < LSB of bit range: 0:3
%Error: Exiting due to.*',
	 );

ok(1);
1;
