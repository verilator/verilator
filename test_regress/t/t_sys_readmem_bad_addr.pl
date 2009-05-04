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
	 fails=>$Self->{v3},
	 expect=>
'%Error: t/t_sys_readmem_bad_addr.mem:\d+: \$readmem file address beyond bounds of array',
     );

ok(1);
1;
