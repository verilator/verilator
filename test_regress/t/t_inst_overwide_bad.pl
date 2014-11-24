#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2004 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_inst_overwide.v");

compile (
	 v_flags2 => ["--lint-only"],
	 make_top_shell=>0,
	 verilator_flags=> [qw(-cc)],
	 verilator_make_gcc=>0,
	 fails=>$Self->{v3},
	 expect=>
q{%Warning-WIDTH: t/t_inst_overwide.v:\d+: Output port connection 'outy_w92' expects 92 bits on the pin connection, but pin connection's VARREF 'outc_w30' generates 30 bits.
%Warning-WIDTH: Use .* to disable this message.
%Warning-WIDTH: t/t_inst_overwide.v:\d+: Output port connection 'outz_w22' expects 22 bits on the pin connection, but pin connection's VARREF 'outd_w73' generates 73 bits.
%Warning-WIDTH: t/t_inst_overwide.v:\d+: Input port connection 'inw_w31' expects 31 bits on the pin connection, but pin connection's VARREF 'ina_w1' generates 1 bits.
%Warning-WIDTH: t/t_inst_overwide.v:\d+: Input port connection 'inx_w11' expects 11 bits on the pin connection, but pin connection's VARREF 'inb_w61' generates 61 bits.
%Error: Exiting due to.*},
	 );

ok(1);
1;
