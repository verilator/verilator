#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_trace_public.v");

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
    make_top_shell => 0,
    make_main => 0,
    v_flags2 => ["-DPUB_FUNC --trace --exe $Self->{t_dir}/$Self->{name}.cpp"],
    );

execute (
    check_finished=>1,
    );

vcd_identical ("$Self->{obj_dir}/simx.vcd",
	       "t/t_trace_public.out");

ok(1);
1;
