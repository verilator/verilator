#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# test whether json dumps don't "crash" astsee

scenarios(vlt => 1);

{
    my $cmd = qq{astsee_verilator -h >/dev/null 2>&1};
    print "\t$cmd\n" if $::Debug;
    system($cmd) and do { skip("No astsee installed\n"); return 1 }
}

top_filename("t/t_EXAMPLE.v");

lint(
    v_flags => ["--lint-only --dump-tree-json"],
    );


run(cmd => ["cd $Self->{obj_dir} && astsee_verilator *001*.json > astsee.log"],
    logfile => "$Self->{obj_dir}/astsee.log");

ok(1);

1;
