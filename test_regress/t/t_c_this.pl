#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2021 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

compile();

if ($Self->{vlt_all}) {
    # The word 'this' (but only the whole word 'this' should have been replaced
    # in the contents.
    my $file = glob_one("$Self->{obj_dir}/$Self->{VM_PREFIX}___024root__DepSet_*__0.cpp");
    my $text = file_contents($file);
    error("$file has 'this->clk'") if ($text =~ m/\bthis->clk\b/);
    error("$file does not have 'xthis'") if ($text !~ m/\bxthis\b/);
    error("$file does not have 'thisx'") if ($text !~ m/\bthisx\b/);
    error("$file does not have 'xthisx'") if ($text !~ m/\bxthisx\b/);
}

ok(1);
1;
