#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 );

execute (
	 fails=>$Last_Self->{v3},
	 expect=>
'%Error: t/t_sys_readmem_bad_digit.mem:\d+: \$readmemb \(binary\) file contains hex characters',
     );

ok(1);
1;
