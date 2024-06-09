#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_flag_main.v");

compile(
    verilator_flags2 => ['--binary --runtime-debug'],
    );

execute(
    check_finished => 1,
    aslr_off => 1,  # Some GCC versions hit an address-sanitizer bug otherwise
    );

file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.mk", qr/VL_DEBUG=1/);

ok(1);
1;
