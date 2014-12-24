#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
    v_flags2 => ["--lint-only -Wwarn-style -Wno-DECLFILENAME"],
    fails=>1,
    verilator_make_gcc => 0,
    make_top_shell => 0,
    make_main => 0,
    expect=>
quotemeta(
'%Warning-COMBDLY: t/t_lint_latch_bad.v:24: Delayed assignments (<=) in non-clocked (non flop or latch) block; suggest blocking assignments (=).
%Warning-COMBDLY: Use "/* verilator lint_off COMBDLY */" and lint_on around source to disable this message.
%Warning-COMBDLY: *** See the manual before disabling this,
%Warning-COMBDLY: else you may end up with different sim results.
%Error: Exiting due to 1 warning').'.*',
    );

ok(1);
1;

