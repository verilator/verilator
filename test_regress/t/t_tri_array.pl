#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

# When fix, update ifdefs in t_sv_cpu files; search for t_tri_array
$Self->{vlt_all} and unsupported("Verilator unsupported, tristate arrays");

compile(
    );

execute(
    check_finished => 1,
    );

ok(1);
1;
