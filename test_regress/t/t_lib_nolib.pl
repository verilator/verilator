#!/usr/bin/env perl
# Makes the test run with tracing enabled by default, can be overridden
# with --notrace
unshift(@ARGV, "--trace");
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Todd Strader. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(
    vlt => 1,
    xsim => 1,
    );

$Self->{sim_time} = $Self->{benchmark} * 100 if $Self->{benchmark};
top_filename("t/t_lib_prot.v");

# Tests the same code as t_lib_prot.pl but without --protect-lib
compile(
    verilator_flags2 => ["t/t_lib_prot_secret.v"],
    xsim_flags2 => ["t/t_lib_prot_secret.v"],
    );

execute(
    check_finished => 1,
    );

if ($Self->{vlt} && $Self->{trace}) {
    # We can see the ports of the secret module
    file_grep("$Self->{obj_dir}/simx.vcd", qr/accum_in/);
    # and we can see what's inside (because we didn't use --protect-lib)
    file_grep("$Self->{obj_dir}/simx.vcd", qr/secret_/);
}

ok(1);
1;
