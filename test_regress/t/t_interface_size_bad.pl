#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	fails=>1,
	expect=>
q{%Error: t/t_interface_size_bad.v:\d+: Illegal IFACEREF port connection 'foo', mismatch between port which is an interface array of size 5, and expression which is an interface array of size 4.
%Error: t/t_interface_size_bad.v:\d+: Illegal IFACEREF port connection 'foo', mismatch between port which is an interface array of size 5, and expression which is an interface array of size 6.
%Error: Exiting due to.*},
    );

ok(1);
1;
