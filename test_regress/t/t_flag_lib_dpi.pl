#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2023 by Shupei Fan.
# SPDX-License-Identifier: CC0-1.0

scenarios(vlt => 1);

run(logfile => "$Self->{obj_dir}/vlt_compile.log",
    cmd => ["perl",
            "$ENV{VERILATOR_ROOT}/bin/verilator",
            "-cc",
            "--build",
            '--no-timing',
            "-Mdir",
            "$Self->{obj_dir}",
            "t/t_flag_lib_dpi.v",
            "$Self->{t_dir}/t_flag_lib_dpi.cpp",
            "$Self->{t_dir}/t_flag_lib_dpi_main.cpp"],
    verilator_run => 1,
    );

run(logfile => "$Self->{obj_dir}/cxx_compile.log",
    cmd => ["cd $Self->{obj_dir}"
            . " && cp $Self->{t_dir}/t_flag_lib_dpi.mk t_flag_lib_dpi.mk"
            . " && $ENV{MAKE} -f t_flag_lib_dpi.mk t_flag_lib_dpi_test"
            . " && ./t_flag_lib_dpi_test"],
    check_finished => 1,
    );

ok(1);
1;
