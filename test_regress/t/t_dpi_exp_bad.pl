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
    fails => $Self->{vlt_all},
    expect =>
'%Error: t/t_dpi_exp_bad.v:\d+: DPI functions cannot return > 32 bits or four-state; use a two-state type or task instead: dpix_f_bit48__Vfuncrtn
%Error: Exiting due to .*'
    );

ok(1);
1;
