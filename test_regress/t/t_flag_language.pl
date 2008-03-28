#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }

compile (
	 verilator_flags2 => ['--language 1364-2001'],
	 );

execute (
	 check_finished=>1,
     );

ok(1);
1;
