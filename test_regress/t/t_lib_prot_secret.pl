#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Todd Strader. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

compile (
    verilator_flags2 => ["--protect-lib",
                         "secret",
                         "--protect-key",
                         "SECRET_FAKE_KEY"],
    verilator_make_gcc => 0,
    verilator_make_gmake => 0,
    make_main => 0,
    make_top_shell => 0,
    );

run(cmd=>[$ENV{MAKE},
          "-C",
          "$Self->{obj_dir}",
          "-f",
          "V$Self->{name}.mk"]);

ok(1);
1;
