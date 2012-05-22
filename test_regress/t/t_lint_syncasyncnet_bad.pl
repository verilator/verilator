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
    v_flags2 => ["--lint-only -Wall -Wno-DECLFILENAME --if-depth 10"],
    fails=>1,
    verilator_make_gcc => 0,
    make_top_shell => 0,
    make_main => 0,
    expect=>
'%Warning-SYNCASYNCNET: t/t_lint_syncasyncnet_bad.v:\d+: Signal flopped as both synchronous and async: rst_both_l
%Warning-SYNCASYNCNET: t/t_lint_syncasyncnet_bad.v:\d+: ... Location of async usage
%Warning-SYNCASYNCNET: t/t_lint_syncasyncnet_bad.v:\d+: ... Location of sync usage
%Warning-SYNCASYNCNET: Use .* around source to disable this message.
%Error: Exiting due to.*',
    );

ok(1);
1;

