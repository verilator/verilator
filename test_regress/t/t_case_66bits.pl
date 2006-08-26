#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }

compile (
	 );

execute (
	 check_finished=>1,
     );

ok(1);
1;
