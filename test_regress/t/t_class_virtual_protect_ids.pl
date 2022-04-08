#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2021 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

# This test makes randomly named .cpp/.h files, which tend to collect, so remove them first
foreach my $filename (glob ("$Self->{obj_dir}/*_PS*.cpp"
                            . " $Self->{obj_dir}/*_PS*.h"
                            . " $Self->{obj_dir}/*.d")) {
    print "rm $filename\n" if $Self->{verbose};
    unlink $filename;
}

top_filename("t/t_class_virtual.v");

compile(
    verilator_flags2 => ["--protect-ids",
                         "--protect-key SECRET_KEY"]
    );

execute(
    check_finished => 1,
    );

ok(1);
1;
