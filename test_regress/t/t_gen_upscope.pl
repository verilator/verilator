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
q{created tag with scope = top.t.b.gen[0].tag
created tag with scope = top.t.b.gen[1].tag
created tag with scope = top.t.tag
mod a has scope = top.t
mod a has tag   = top.t.tag
mod b has scope = top.t.b
mod b has tag   = top.t.tag
mod c has scope = top.t.b.gen[0].c
mod c has tag   = top.t.b.gen[0].tag
mod c has scope = top.t.b.gen[1].c
mod c has tag   = top.t.b.gen[1].tag
*-* All Finished *-*}),
    );

ok(1);
1;
