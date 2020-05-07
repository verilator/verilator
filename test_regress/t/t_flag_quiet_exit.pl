#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Todd Strader. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

top_filename("t/t_file_does_not_exist.v");

# Tests for the error message and then the absence of the
# "Command Failed" line
compile(
    v_flags2 => ["--quiet-exit"],
    fails => 1,
    );

file_grep_not("$Self->{obj_dir}/vlt_compile.log", qr/Exiting due to/);
file_grep_not("$Self->{obj_dir}/vlt_compile.log", qr/Command Failed/);

ok(1);
1;
