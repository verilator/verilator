#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(linter => 1);

lint(
    verilator_flags2 => ["--lint-only -Wwarn-VARHIDDEN"],
    fails => $Self->{vlt_all},
    expect_filename => $Self->{golden_filename},
    );

extract(
    in => $Self->{top_filename},
    out => "../docs/gen/ex_VARHIDDEN_faulty.rst",
    regexp => qr/(module t|integer|endmodule)/);

extract(
    in => $Self->{golden_filename},
    out => "../docs/gen/ex_VARHIDDEN_msg.rst",
    lineno_adjust => -6,
    regexp => qr/(var_bad_hide)/);

ok(1);
1;
