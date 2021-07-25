#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_param_in_func.v");

compile(
    verilator_flags2 => ["--stats", "+define+NO_INLINE=1"],
    );

execute(check_finished => 1);

# The parameter array should have been put in the constant pool
if ($Self->{vlt_all}) {
    file_grep($Self->{stats}, qr/ConstPool, Tables emitted\s+(\d+)/i, 3);
}

# Shouldn't have any references to the parameter array
foreach my $file (
      glob_all("$Self->{obj_dir}/$Self->{VM_PREFIX}*.h"),
      glob_all("$Self->{obj_dir}/$Self->{VM_PREFIX}*.cpp")
    ) {
    file_grep_not($file, qr/digits/i);
}

ok(1);
1;
