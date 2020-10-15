#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

use File::Copy;

scenarios(dist => 1);

my $tmp = "$Self->{obj_dir}/copied.dat";
File::Copy::copy("$Self->{t_dir}/t_vlcov_data_a.dat", $tmp);

run(cmd => ["../bin/verilator_coverage",
            "--unlink",
            $tmp,
            "--write", "$Self->{obj_dir}/output.dat"],
    verilator_run => 1,
    );

files_identical("$Self->{obj_dir}/output.dat", "t/t_vlcov_data_a.dat");

# --unlink should have removed it
!-r $tmp or error("Not unlinked");

ok(1);

1;
