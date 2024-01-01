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

compile(
    verilator_flags2 => ['-fno-gate'],
    );

execute(
    check_finished => 1,
    expect_filename => $Self->{golden_filename},
    );

# Check for coverage on all POW functions
system("cat $Self->{obj_dir}/$Self->{vm_prefix}_*.cpp > $Self->{obj_dir}/all.cpp");

file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POW_III/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POW_IIQ/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POW_IIW/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POW_QQI/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POW_QQQ/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POW_QQW/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POW_WWI/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POW_WWQ/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POW_WWW/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POWSS_III/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POWSS_IIQ/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POWSS_IIW/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POWSS_QQI/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POWSS_QQQ/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POWSS_QQW/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POWSS_WWI/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POWSS_WWQ/);
file_grep("$Self->{obj_dir}/all.cpp", qr/VL_POWSS_WWW/);

ok(1);
1;
