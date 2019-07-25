#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(simulator => 1);

compile(
    python => 1,
    verilator_make_gmake => 0,
    verilator_make_cmake => 1,
    cmake_flags => "-DTEST_CMAKE_OVERRIDE_SCRIPT=$Self->{t_dir}/t_python_cmake.cmake",
    );

if ($Self->have_pybind11 && $Self->have_cmake) {
    run(logfile => "$Self->{obj_dir}/vlt_python.log",
        cmd     => [ "python3 $Self->{t_dir}/t_python_cmake.py $Self->{obj_dir}" ]);
}

ok(1);
1;
