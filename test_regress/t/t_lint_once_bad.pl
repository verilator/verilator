#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(vlt_all => 1);

compile(
    verilator_flags2 => ["--lint-only -Wwarn-UNUSED"],
    verilator_make_gcc => 0,
    make_top_shell => 0,
    make_main => 0,
    fails => 1,
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
