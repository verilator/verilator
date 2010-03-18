#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

$Self->_run(fails=>1,
		 cmd=>["perl","../bin/verilator",
		       "--help"],
		 logfile=>"$Self->{obj_dir}/t_help.log",
		 tee=>0,
	    );

file_grep ("$Self->{obj_dir}/t_help.log", qr/DISTRIBUTION/i);

ok(1);
1;
