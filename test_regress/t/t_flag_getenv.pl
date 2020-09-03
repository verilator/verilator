#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

setenv('FOOBARTEST', "gotit");

run(
    cmd => ["../bin/verilator --getenv FOOBARTEST"],
    expect => 'gotit
',
    logfile => "$Self->{obj_dir}/simx.log",
    verilator_run => 1,
    );

foreach my $var (qw(MAKE PERL SYSTEMC SYSTEMC_ARCH SYSTEMC_LIBDIR VERILATOR_ROOT)) {
    run(
        cmd => ["../bin/verilator --getenv ${var}"],
        logfile => "$Self->{obj_dir}/simx.log",
        verilator_run => 1,
        );
}

ok(1);
1;
