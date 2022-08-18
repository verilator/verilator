#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2022 by Antmicro Ltd. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

compile(
    # do not test classes for multithreaded, as V3InstrCount doesn't handle MemberSel
    verilator_flags2 => $Self->{vltmt} ? ['-DNO_CLASS'] : [],
    );

execute(
    check_finished => 1,
    );

for my $file (glob_all("$Self->{obj_dir}/$Self->{VM_PREFIX}*.cpp")) {
    # Check that these simple expressions are not stored in temp variables
    file_grep_not($file, qr/__Vtrigcurr__expression_.* = vlSelf->clk;/);
    file_grep_not($file, qr/__Vtrigcurr__expression_.* = vlSelf->t__DOT__q.at\(0U\);/);
    file_grep_not($file, qr/__Vtrigcurr__expression_.* = .*vlSelf->t__DOT____Vcellinp__u_array__t/);
    file_grep_not($file, qr/__Vtrigcurr__expression_.* = .*vlSymsp->TOP__t__DOT__u_class.__PVT__obj/);
    # The line below should only be generated if concats/replicates aren't converted to separate senitems
    file_grep_not($file, qr/__Vtrigcurr__expression_.* = .*vlSelf->t__DOT__a/);
}

ok(1);
1;
