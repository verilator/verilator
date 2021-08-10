#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2010-2011 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

my $stdout_filename = "$Self->{obj_dir}/$Self->{name}__test.vpp";

compile(
    verilator_flags2 => ['-E --pipe-filter \'python3 t/t_pipe_filter.pf\' '],
    verilator_make_gmake => 0,
    make_top_shell => 0,
    make_main => 0,
    stdout_filename => $stdout_filename,
    );

files_identical($stdout_filename, $Self->{golden_filename});

ok(1);
1;
