#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(dist => 1);

run(cmd => ["cd $Self->{obj_dir} && $ENV{VERILATOR_ROOT}/bin/verilator_gantt"
            . " $Self->{t_dir}/$Self->{name}.dat > gantt.log"],
    check_finished => 0);

files_identical("$Self->{obj_dir}/gantt.log", $Self->{golden_filename});

vcd_identical("$Self->{obj_dir}/profile_exec.vcd", "$Self->{t_dir}/$Self->{name}.vcd.out");

ok(1);
1;
