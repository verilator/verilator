#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2004 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

$Self->{cycles} = ($Self->{benchmark} ? 100_000_000 : 100);
$Self->{sim_time} = $Self->{cycles} * 10 + 1000;

compile(
    v_flags2 => ["+define+SIM_CYCLES=$Self->{cycles}",],
    verilator_flags2=>["-Wno-UNOPTTHREADS"],
    );

execute(
    );

ok(1);
1;
