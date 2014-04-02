#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
    );

execute (
    check_finished=>1,
	 expect=>quotemeta(
q{created tag with scope = top.v.b.gen[0].tag
created tag with scope = top.v.b.gen[1].tag
created tag with scope = top.v.tag
mod a has scope = top.v
mod a has tag   = top.v.tag
mod b has scope = top.v.b
mod b has tag   = top.v.tag
mod c has scope = top.v.b.gen[0].c
mod c has tag   = top.v.b.gen[0].tag
mod c has scope = top.v.b.gen[1].c
mod c has tag   = top.v.b.gen[1].tag
*-* All Finished *-*}),
    );

ok(1);
1;
