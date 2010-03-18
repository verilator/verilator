#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{golden_out} ||= "t/$Self->{name}.out";

compile (
	 verilator_flags2 => ["--stats --O3 -x-assign fast"],
	 );

execute (
	 check_finished=>1,
     );

ok(files_identical("$Self->{obj_dir}/$Self->{name}_logger.log", $Self->{golden_out}));
1;
