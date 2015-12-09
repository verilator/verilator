#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2004 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
    v_flags2 => ["--lint-only"],
    fails=>1,
    expect=>
'%Warning-WIDTHCONCAT: t/t_concat_large_bad.v:\d+: More than a 8k bit replication is probably wrong: 32768
%Warning-WIDTHCONCAT: Use .*
%Error: Exiting due to.*',
    );

ok(1);
1;
