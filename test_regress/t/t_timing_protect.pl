#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2022 by Antmicro Ltd. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

if (!$Self->have_coroutines) {
    skip("No coroutine support");
}
else {
    top_filename("t/t_timing_fork_join.v");  # Contains all relevant constructs

    compile(
        verilator_flags2 => ["--exe --main --timing --protect-ids",
                             "--protect-key SECRET_KEY"],
        make_main => 0,
        );

    execute(
        check_finished => 1,
        );

    if ($Self->{vlt_all}) {
        # Check for secret in any outputs
        my $any;
        foreach my $filename (glob $Self->{obj_dir} . "/*.[ch]*") {
            file_grep_not($filename, qr/event[123]/i);
            file_grep_not($filename, qr/t_timing_fork_join/i);
            $any = 1;
    }
    $any or $Self->error("No outputs found");

}

}

ok(1);
1;
