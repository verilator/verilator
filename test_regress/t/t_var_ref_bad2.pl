#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(simulator => 1);

compile(
    v_flags2 => ["--lint-only"],
    make_top_shell => 0,
    make_main => 0,
    verilator_make_gcc => 0,
    fails => 1,
    expect =>
q{%Error: t/t_var_ref_bad2.v:\d+: Assigning to const ref variable: bad_const_set
%Error: t/t_var_ref_bad2.v:\d+: Ref argument requires matching types; port 'int_ref' requires VAR 'int_ref' but connection is VARREF 'bad_non_int'.
.*%Error: Exiting due to.*},
    );

ok(1);
1;
