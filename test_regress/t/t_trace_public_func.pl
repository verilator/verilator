#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_trace_public.v");

if ($Last_Self->{v3}) {
    compile (
	     make_top_shell => 0,
	     make_main => 0,
	     v_flags2 => ["-DPUB_FUNC --trace --exe t/$Last_Self->{name}.cpp"],
	     );

    execute (
	     check_finished=>1,
	     );

    ok(vcd_identical ("obj_dir/$Last_Self->{name}_simx.vcd",
		      "t/$Last_Self->{name}.out"));
}
else {
    ok(1);
}
1;
