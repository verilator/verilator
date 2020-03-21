#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

compile(
    );

execute(
    all_run_flags => ["+verilator+debug +verilator+debugi+9 +verilator+rand+reset+1"],
    check_finished => 1,
    expect => (q{.*Verilated::debug is on.*}),
    );

execute(
    all_run_flags => ["+verilator+help"],
    fails => 1,
    expect => (
q{.*For help, please see 'verilator --help'
.*}),
     );

execute(
    all_run_flags => ["+verilator+V"],
    fails => 1,
    expect => (
q{.*Version:}),
     );

execute(
    all_run_flags => ["+verilator+version"],
    fails => 1,
    expect => (
q{.*Version:}),
     );

ok(1);

1;
