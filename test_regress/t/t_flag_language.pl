#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }

compile (
	 verilator_flags2 => ['--language 1364-2001'],
	 );

execute (
	 check_finished=>1,
     );

ok(1);
1;
