#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2023 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

compile(
    v_flags2 => ["--timing",
                 "-Wno-PKGNODECL -Wno-IMPLICITSTATIC -Wno-CONSTRAINTIGN -Wno-MISINDENT",
                 "-Wno-CASEINCOMPLETE -Wno-CASTCONST -Wno-SYMRSVDWORD -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC",
                 "-Wno-REALCVT", # TODO note mostly related to $realtime - could suppress or fix upstream
                 "-Wno-ZERODLY", # TODO issue #4494, add support
                 ],
    verilator_make_gmake => 0,
    );

#execute(
#    check_finished => 1,
#    );

ok(1);
1;
