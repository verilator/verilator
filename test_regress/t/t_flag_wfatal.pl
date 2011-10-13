#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_flag_wfatal.v");

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
    v_flags2 => ["--lint-only -Wno-fatal"],
    fails=>0,
    verilator_make_gcc => 0,
    make_top_shell => 0,
    make_main => 0,
    expect=>
q{%Warning-WIDTH: t/t_flag_wfatal.v:\d+: Operator ASSIGNW expects 4 bits on the Assign RHS, but Assign RHS.s CONST '6'h2e' generates 6 bits.
%Warning-WIDTH: Use .* and lint_on around source to disable this message.
},
    );

ok(1);
1;
