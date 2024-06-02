#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

compile(
    timing_loop => 1,
    verilator_flags2 => ["--timing --output-split-cfuncs 1 -CFLAGS -Werror"],
    );

execute(
    check_finished => 1,
    );

check_splits();

ok(1);
1;

sub check_splits {
    my $got1;
    my $gotSyms1;
    return if !$Self->have_coroutines;
    foreach my $file (glob("$Self->{obj_dir}/*.cpp")) {
        if ($file =~ /Syms__1/) {
            $gotSyms1 = 1;
        } elsif ($file =~ /__1/) {
            $got1 = 1;
        }
    }
    $got1 or error("No __1 split file found");
    $gotSyms1 or error("No Syms__1 split file found");
}
