#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2012 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

my $out_filename = "$Self->{obj_dir}/$Self->{name}_waiver_gen.vlt";
my $waiver_filename = "$Self->{obj_dir}/$Self->{name}_waiver.vlt";

compile(
    v_flags2 => ['--waiver-output', $out_filename],
    fails => 1,
    );

files_identical("$out_filename", $Self->{golden_filename});

file_sed($out_filename, $waiver_filename,
         sub { s/\/\/ lint_off/lint_off/g; });

compile(
    v_flags2 => [$waiver_filename],
    );

ok(1);
1;
