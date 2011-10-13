#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_tri_gate.v");

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
	 make_top_shell => 0,
	 make_main => 0,
	 v_flags2 => ['+define+T_BUFIF1',],
	 make_flags => 'CPPFLAGS_ADD=-DT_BUFIF1',
	 verilator_flags2 => ["--exe $Self->{t_dir}/t_tri_gate.cpp"],
    );

execute (
	 check_finished=>1,
    );

ok(1);
1;
