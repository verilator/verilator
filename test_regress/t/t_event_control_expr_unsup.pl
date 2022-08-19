#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2022 by Antmicro Ltd. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);  # no vltmt, as AstMemberSel is unhandled in V3InstrCount

top_filename("t_event_control_expr.v");

compile(
    verilator_flags2 => ['-DUNSUP'],
    fails => 1,
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
