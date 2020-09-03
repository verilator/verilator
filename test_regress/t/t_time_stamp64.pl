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

# Verilator before 4.033 had 'double sc_time_stamp()', make sure new form compiles
$self->{vl_time_stamp64} = 1;

compile(
    verilator_flags2 => ['-DVL_TIME_STAMP64=1'],
    );

execute(
    check_finished => 1,
    );

ok(1);

1;
