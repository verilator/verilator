#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

# Use --debug-protect to assist debug

compile(
    );

execute(
    check_finished => 1,
    );

if ($Self->{vlt_all}) {
    # Check for unused structs in any outputs
    my $any;
    foreach my $filename (glob $Self->{obj_dir} . "/*.[ch]*") {
        file_grep_not($filename, qr/useless/i);
        $any = 1;
    }
    $any or $Self->error("No outputs found");
}

ok(1);
1;
