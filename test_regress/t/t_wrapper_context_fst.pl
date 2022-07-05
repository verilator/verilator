#!/usr/bin/env perl
if (!$::Driver) { use strict; use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Multiple Model Test Module
#
# Copyright 2020-2021 by Andreas Kuster. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

top_filename("t/t_wrapper_context.v");

compile(
    make_top_shell => 0,
    make_main => 0,
    # link threads library, add custom .cpp code, add tracing & coverage support
    verilator_flags2 => ["--exe $Self->{t_dir}/t_wrapper_context.cpp",
                         "--trace-fst --coverage -cc"],
    threads => 1,
    make_flags => 'CPPFLAGS_ADD=-DVL_NO_LEGACY',
    );

execute(
    check_finished => 1,
    );

ok(1);
1;
