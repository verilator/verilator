#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
    v_flags2 => ["--lint-only"],
    fails=>$Self->{v3},
    expect=>
q{%Warning-LITENDIAN: t/t_interface_array_nocolon_bad.v:\d+: Little endian cell range connecting to vector: MSB < LSB of cell range: 0:2
%Warning-LITENDIAN: Use [^\n]+
%Warning-LITENDIAN: t/t_interface_array_nocolon_bad.v:\d+: Little endian cell range connecting to vector: MSB < LSB of cell range: 1:3
%Warning-LITENDIAN: t/t_interface_array_nocolon_bad.v:\d+: Little endian cell range connecting to vector: MSB < LSB of cell range: 0:2
%Warning-LITENDIAN: t/t_interface_array_nocolon_bad.v:\d+: Little endian cell range connecting to vector: MSB < LSB of cell range: 1:3
%Error: Exiting due to},
    );

ok(1);
1;
