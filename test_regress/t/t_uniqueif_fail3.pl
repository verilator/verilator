#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_uniqueif.v");

compile (
    v_flags2 => ['+define+FAILING_ASSERTION3'],
    verilator_flags2 => ['--assert'],
    nc_flags2 => ['+assert'],
    fails => $Self->{nc},
    );

execute (
    fails => $Self->{vlt},
    expect=>
'.*%Error: t_uniqueif.v:\d+: Assertion failed in top.v: \'unique if\' statement violated
%Error: t/t_uniqueif.v:\d+: Verilog \$stop
.*',
    );

ok(1);
1;
