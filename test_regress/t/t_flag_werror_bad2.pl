#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_flag_werror.v");

compile (
	 fails=>$Last_Self->{v3},
	 verilator_flags=> [qw(-sp -Werror-WIDTH)],
	 expect=>
'%Error: t/t_flag_werror.v:\d+: Operator ASSIGNW expects 4 bits on the Assign RHS, but Assign RHS.s CONST generates 6 bits.
%Error: Exiting due to',
	 ) if $Last_Self->{v3};

ok(1);
1;
