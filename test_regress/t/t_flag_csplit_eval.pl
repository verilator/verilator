#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

sub check_evals {
    my $got = 0;
    foreach my $file (glob("$Self->{obj_dir}/*.cpp")) {
        my $fh = IO::File->new("<$file");
        local $/; undef $/;
        my $wholefile = <$fh>;

        if ($wholefile =~ /___eval__[0-9]+\(.*\)\s*{/) {
            ++$got;
        }
    }
    $got >= 2 or error("Too few _eval functions found: $got");
}

scenarios(vlt_all => 1);

compile(
    v_flags2 => ["--output-split 1 --output-split-cfuncs 20"],
    verilator_make_gmake => 0, # Slow to compile, so skip it
    );

check_evals();

ok(1);
1;
