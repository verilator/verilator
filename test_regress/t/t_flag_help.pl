#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(dist => 1);

foreach my $prog (
    # See also t_flag_version.pl
    "../bin/verilator",
    "../bin/verilator_coverage",
    "../bin/verilator_difftree",
    "../bin/verilator_gantt",
    "../bin/verilator_profcfunc",
    ) {
    run(fails => 0,
        cmd => ["perl", $prog,
                "--help"],
        logfile => "$Self->{obj_dir}/t_help.log",
        tee => 0,
        );
    file_grep("$Self->{obj_dir}/t_help.log", qr/DISTRIBUTION/i);
}

ok(1);
1;
