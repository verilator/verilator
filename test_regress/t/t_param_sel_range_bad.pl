#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

# Really we shouldn't need to warn in this case.
# When supported, make a new test case that checks the warning
#$Self->{vlt} and $Self->unsupported("Verilator unsupported, bug477");

top_filename("t/t_param_sel_range.v");

compile (
    v_flags2 => ["--lint-only"],
    fails=>1,
    verilator_make_gcc => 0,
    make_top_shell => 0,
    make_main => 0,
    expect=>
'%Warning-SELRANGE: t/t_param_sel_range.v:\d+: Selection index out of range: 7:7 outside 4:0
%Warning-SELRANGE: Use .* to disable this message.
%Error: Exiting due to.*',
    );

ok(1);
1;
