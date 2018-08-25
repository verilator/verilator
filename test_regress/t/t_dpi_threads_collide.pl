#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2018 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(vltmt => 1);

top_filename("t/t_dpi_threads.v");

compile(
    v_flags2 => ["t/t_dpi_threads_c.cpp --threads-dpi all --no-threads-coarsen"],
    );

# Similar to t_dpi_threads, which confirms that Verilator can prevent a
# race between DPI import calls, this test confirms that the race exists
# and that the DPI C code can detect it under --threads-dpi all
# mode.
#
execute(
    fails => 1,
    );

ok(1);
1;
