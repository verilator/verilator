#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(vlt_all => 1);

compile(
    fails => 1,
    expect =>
'%Error: t/t_past_bad.v:\d+:.* \$past tick value must be constant and >= 1 \(IEEE 2017 16.9.3\)
%Warning-TICKCOUNT: t/t_past_bad.v:\d+: \$past tick value of 10000 may have a large performance cost
.*%Error: Exiting due to.*',
    );

ok(1);
1;

