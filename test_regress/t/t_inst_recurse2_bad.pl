#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2004 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
    fails=>1,
    expect=>
'.*%Error: t/t_inst_recurse2_bad.v:\d+: Unsupported: Identically recursive module \(module instantiates itself, without changing parameters\): looped
%Error: Exiting due to.*',
    );

ok(1);
1;
