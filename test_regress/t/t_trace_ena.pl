#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2005 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 v_flags2 => [$Last_Self->{v3}?'-trace':''],
	 );

execute (
	 check_finished=>1,
	 );

if ($Last_Self->{v3}) {
    file_grep     ("obj_dir/Vt_trace_ena__Trace__Slow.cpp", qr/c_trace_on\"/x);
    file_grep_not ("obj_dir/Vt_trace_ena__Trace__Slow.cpp", qr/_trace_off\"/x);
}

ok(1);
1;
