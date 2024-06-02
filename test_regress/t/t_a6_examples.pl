#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(dist => 1);

$Self->{clean_command} = 'rm -rf ../examples/*/build ../examples/*/obj*';

my @examples = sort(glob("../examples/*"));
for my $example (@examples) {
    run(cmd => ["$ENV{MAKE} -C $example"]);
}

ok(1);
1;
