#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

use File::Basename;

scenarios(dist => 1);

# See also t_flag_version.pl

sub check {
    my $interpreter = shift;
    my $prog = shift;

    my $logfile = "$Self->{obj_dir}/t_help__" . basename($prog) . ".log";

    run(fails => 0,
        cmd => [$interpreter, $prog, "--help"],
        logfile => $logfile,
        tee => 0,
        verilator_run => 1,
        );

    file_grep($logfile, qr/(DISTRIBUTION|usage:)/i);
}

check("perl", "../bin/verilator");
check("perl", "../bin/verilator_coverage");

check("python3", "../bin/verilator_ccache_report");
check("python3", "../bin/verilator_difftree");
check("python3", "../bin/verilator_gantt");
check("python3", "../bin/verilator_profcfunc");

ok(1);
1;
