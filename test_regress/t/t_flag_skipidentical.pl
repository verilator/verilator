#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

{
    compile();

    print "NOTE: use --debugi, as --debug in driver turns off skip-identical\n";

    my $outfile = "$Self->{obj_dir}/V" . $Self->{name} . ".cpp";
    my @oldstats = stat($outfile);
    print "Old mtime=", $oldstats[9], "\n";
    $oldstats[9] or error("No output file found: $outfile\n");

    sleep(2);  # Or else it might take < 1 second to compile and see no diff.

    setenv('VERILATOR_DEBUG_SKIP_IDENTICAL', 1);
    compile();

    my @newstats = stat($outfile);
    print "New mtime=", $newstats[9], "\n";

    ($oldstats[9] == $newstats[9])
        or error("--skip-identical was ignored -- recompiled\n");
}

ok(1);
1;
