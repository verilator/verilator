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
  make_main => 0,
  verilator_make_gmake => 1,
  verilator_flags2 => ["--exe --pins-inout-enables --no-timing -Wno-STMTDLY",
                       "$Self->{t_dir}/$Self->{name}.cpp"]
);
if ($Self->{errors}) {
   print "The compile failed, this is expected, checking the compile log...\n";
}

if (files_identical("$Self->{obj_dir}/vlt_gcc.log", "$Self->{golden_filename}", 'logfile')) {
  print "The logfile was as expected\n";
  $Self->{errors} = 0;
  ok(1);
} else {
  ok(0);
}
1;
