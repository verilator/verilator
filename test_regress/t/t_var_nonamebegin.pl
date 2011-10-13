#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
    verilator_flags2 => ['-trace'],
    );

execute (
	 expect=>quotemeta(
'ingen: {mod}.genblk1 top.v.genblk1
d3a: {mod}.d3nameda top.v.d3nameda
b2: {mod} top.v
b3n: {mod}.b3named: top.v.b3named
b3: {mod} top.v
b4: {mod} top.v
t1 {mod}.tsk top.v
t2 {mod}.tsk top.v
*-* All Finished *-*'),
    );

if ($Self->{vlt}) {
    vcd_identical ("$Self->{obj_dir}/simx.vcd",
		   "t/$Self->{name}.out");
}
ok(1);
1;
