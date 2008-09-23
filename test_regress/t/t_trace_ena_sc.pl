#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_trace_ena.v");

compile (
	 v_flags2 => [$Last_Self->{v3}?'-trace -sc':''],
	 );

execute (
	 check_finished=>1,
	 );

if ($Last_Self->{v3}) {
    # Note more checks in _cc.pl
    file_grep     ("obj_dir/$Last_Self->{name}_simx.vcd", qr/\$enddefinitions/x);
}

ok(1);
1;
