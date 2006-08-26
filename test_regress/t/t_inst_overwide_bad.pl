#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id:$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2004 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_inst_overwide.v");

compile (
	 make_top_shell=>0,
	 verilator_flags=> [qw(-sp)],
	 verilator_make_gcc=>0,
	 fails=>$Last_Self->{v3},
	 expect=>
'%Warning-WIDTH: t/t_inst_overwide.v:\d+: Output port connection outy_w92 expects 92 bits but connection\'s VARREF generates 30 bits.
%Warning-WIDTH: Use .* to disable this message.
%Warning-WIDTH: t/t_inst_overwide.v:\d+: Output port connection outz_w22 expects 22 bits but connection\'s VARREF generates 73 bits.
%Warning-WIDTH: t/t_inst_overwide.v:\d+: Input port connection inw_w31 expects 31 bits but connection\'s VARREF generates 1 bits.
%Warning-WIDTH: t/t_inst_overwide.v:\d+: Input port connection inx_w11 expects 11 bits but connection\'s VARREF generates 61 bits.
%Error: Exiting due to.*',
	 );

ok(1);
1;
