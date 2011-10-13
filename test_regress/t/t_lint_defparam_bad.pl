#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_lint_defparam.v");

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
    v_flags2 => ["--lint-only -Wwarn-style -Wno-DECLFILENAME"],
    fails=>1,
    verilator_make_gcc => 0,
    make_top_shell => 0,
    make_main => 0,
    expect=>
'%Warning-DEFPARAM: t/t_lint_defparam.v:\d+: Suggest replace defparam with Verilog 2001 #\(.P\(...etc...\)\)
%Warning-DEFPARAM: Use .* to disable this message.
%Error: Exiting due to.*',
    );

ok(1);
1;

