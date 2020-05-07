#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

compile(
    # Access is so we can dump waves
    v_flags2 => [$Self->{vlt_all} ? '-trace' : ' +access+rwc'],
    );

execute(
    check_finished => 1,
    );

if ($Self->{vlt_all}) {
    file_grep     ("$Self->{obj_dir}/simx.vcd", qr/\$enddefinitions/x);
    my $sig = quotemeta("bra[ket]slash/dash-colon:9");
    file_grep     ("$Self->{obj_dir}/simx.vcd", qr/ $sig/);
    file_grep     ("$Self->{obj_dir}/simx.vcd", qr/ other\.cyc /);
    file_grep     ("$Self->{obj_dir}/simx.vcd", qr/ module mod\.with_dot /);
    vcd_identical ("$Self->{obj_dir}/simx.vcd",
                   $Self->{golden_filename});
}

ok(1);
1;
