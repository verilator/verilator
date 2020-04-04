#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# This test tests CMake support for SystemC

scenarios(simulator => 1);

compile(
    verilator_make_gmake => 0,
    verilator_make_cmake => 1,
    verilator_flags2 => ["-sc"],
    );

execute(
    check_finished => 1,
    );

ok(1);
1;
