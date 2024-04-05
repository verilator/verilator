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

top_filename("t/t_dump.v");

lint(
    v_flags => ["--dump-tree-json --no-json-edit-nums"],
    );

files_identical("$Self->{obj_dir}/Vt_dump_json_001_cells.tree.json", $Self->{golden_filename}, 'logfile');

ok(1);

1;
