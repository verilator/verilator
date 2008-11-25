#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

unlink("$Self->{obj_dir}/t_sys_file_scan_test.log");

compile (
	 );

execute (
	 check_finished=>1,
     );

file_grep ("$Self->{obj_dir}/t_sys_file_scan_test.log",
"# a
          1
");

ok(1);
1;
