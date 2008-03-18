#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2007 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

$Last_Self->_run(fails=>1,
		 cmd=>["perl","../bin/verilator",
		       "--help"],
		 logfile=>"obj_dir/t_help.log",
		 tee=>0,
		 ) if $Last_Self->{v3};

file_grep ("obj_dir/t_help.log", qr/DISTRIBUTION/i);

ok(1);
1;
