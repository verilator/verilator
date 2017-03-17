#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2005 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
    verilator_flags2 => ["--lint-only"],
    verilator_make_gcc => 0,
    make_top_shell => 0,
    make_main => 0,
    fails => 1,
    # Used to be %Error: t/t_order_wireloop.v:\d+: Wire inputs its own output, creating circular logic .wire x=x.
    # However we no longer gate optimize this
    expect=>
q{%Error: t/t_interface_typo_bad.v:\d+: Parent cell's interface is not found: foo_intf
%Error: t/t_interface_typo_bad.v:\d+: Cannot find file containing interface: fo_intf
%Error: t/t_interface_typo_bad.v:\d+: Found definition of 'the_foo' as a CELL but expected a variable
.*},
	 );

ok(1);
1;
