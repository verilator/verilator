#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2021 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

compile();

if ($Self->{vlt_all}) {
    # The word 'this' (but only the whole word 'this' should have been replaced
    # in the contents.
    my $has_this   = 0;
    my $has_xthis  = 0;
    my $has_thisx  = 0;
    my $has_xthisx = 0;
    for my $file (glob_all("$Self->{obj_dir}/$Self->{VM_PREFIX}___024root__DepSet_*__0.cpp")) {
        my $text = file_contents($file);
        $has_this   = 1 if ($text =~ m/\bthis->clk\b/);
        $has_xthis  = 1 if ($text =~ m/\bxthis\b/);
        $has_thisx  = 1 if ($text =~ m/\bthisx\b/);
        $has_xthisx = 1 if ($text =~ m/\bxthisx\b/);
    }
    error("Some file has 'this->clk'") if $has_this;
    error("No file has 'xthis'") if !$has_xthis;
    error("No file has 'thisx'") if !$has_thisx;
    error("No file has 'xthisx'") if !$has_xthisx;
}

ok(1);
1;
