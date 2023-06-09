#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

lint(
    v_flags => ["--debug --debugi 1 -Wno-MULTITOP t/t_debug_inputs_b.v"],
    );

file_grep("$Self->{obj_dir}/V$Self->{name}__inputs.vpp", qr/module t_debug_inputs /);
file_grep("$Self->{obj_dir}/V$Self->{name}__inputs.vpp", qr/module t_debug_inputs_a /);
file_grep("$Self->{obj_dir}/V$Self->{name}__inputs.vpp", qr/module t_debug_inputs_b /);

ok(1);
1;
