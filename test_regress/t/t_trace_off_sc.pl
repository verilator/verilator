#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2007 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_trace_ena.v");

compile (
	 v_flags2 => [$Last_Self->{v3}?'-notrace -sc':''],
	 );

execute (
	 check_finished=>1,
	 );

if ($Last_Self->{v3}) {
    !-r "obj_dir/$Last_Self->{name}_simx.vcd" or $Last_Self->error("Tracing should be off\n");
}

ok(1);
1;
