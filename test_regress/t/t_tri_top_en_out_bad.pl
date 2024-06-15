#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

compile(
  make_top_shell => 0,
  make_main => 1,
  verilator_make_gmake => 1,
  verilator_flags2 => ["--exe --pins-inout-enables --no-timing -Wno-STMTDLY"]
);
file_grep_not("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/internal_sub_io__out/);
file_grep_not("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/internal_sub_io__en/);

ok(1);
1;
