#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
    fails=>1,
    expect=>
q{%Error: t/t_array_backw_index_bad.v:\d+: Slice selection '\[1:3\]' has backward indexing versus data type's '\[3:0\]'
%Error: t/t_array_backw_index_bad.v:\d+: Slice selection '\[3:1\]' has backward indexing versus data type's '\[0:3\]'
%Error: t/t_array_backw_index_bad.v:\d+: Slice selection index '\[4:3\]' outside data type's '\[3:0\]'
%Error: t/t_array_backw_index_bad.v:\d+: Slice selection index '\[1:-1\]' outside data type's '\[3:0\]'
.*%Error: Exiting due to.*},
    );

ok(1);
1;
