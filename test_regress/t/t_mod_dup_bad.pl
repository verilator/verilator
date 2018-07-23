#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(vlt_all => 1);

compile(
    fails => 1,
    expect =>
'%Warning-MODDUP: t/t_mod_dup_bad.v:\d+: Duplicate declaration of module: a
%Warning-MODDUP: t/t_mod_dup_bad.v:\d+: ... Location of original declaration
.*
%Error: Exiting due to.*',
    );

ok(1);
1;
