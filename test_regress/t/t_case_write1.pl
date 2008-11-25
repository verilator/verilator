#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

$golden_out ||= "t/$Self->{name}.out";

compile (
	 v_flags2 => [$Self->{v3}?"--stats --O3 -x-assign fast":""],
	 );

execute (
	 check_finished=>1,
     );

ok(files_identical("$Self->{obj_dir}/$Self->{name}_logger.log", $golden_out));
1;
