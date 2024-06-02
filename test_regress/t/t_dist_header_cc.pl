#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


use Cwd;

scenarios(dist => 1);

my $root = "..";

if (!-r "$root/.git") {
    skip("Not in a git repository");
} else {
    run(cmd => ["cd $root/src/obj_dbg && $ENV{MAKE} -j 4 -k -f ../Makefile_obj VL_NOOPT=1 header_cc"],
        check_finished => 0);
}

ok(1);
1;
