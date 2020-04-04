#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

run(cmd => ["cd $Self->{obj_dir}"
            ." && c++ -c ../../t/t_flag_ldflags_a.cpp"
            ." && ar -cr t_flag_ldflags_a.a t_flag_ldflags_a.o"
            ." && ranlib t_flag_ldflags_a.a "],
    check_finished => 0);
run(cmd => ["cd $Self->{obj_dir}"
            ." && c++ -fPIC -c ../../t/t_flag_ldflags_so.cpp"
            ." && c++ -shared -o t_flag_ldflags_so.so -lc t_flag_ldflags_so.o"],
    check_finished => 0);

compile(
    # Pass multiple -D's so we check quoting works properly
    v_flags2 => ["-CFLAGS '-DCFLAGS_FROM_CMDLINE -DCFLAGS2_FROM_CMDLINE' ",
                 "t/t_flag_ldflags_c.cpp",
                 "t_flag_ldflags_a.a",
                 "t_flag_ldflags_so.so",],
    );

execute(
    check_finished => 1,
    run_env => "LD_LIBRARY_PATH=$Self->{obj_dir}",
    );

ok(1);
1;
