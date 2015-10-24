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
	 check_finished=>1,
	 expect=>quotemeta(dequote(
'To stdout
To stderr
*-* All Finished *-*
')),
     );

ok(1);

# Don't put control chars into our source repository, pre-compress instead
sub dequote { my $s = shift; $s =~ s/<#013>/\r/g; $s; }

1;
