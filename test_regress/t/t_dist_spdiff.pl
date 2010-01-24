#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2010 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

my $root = "..";
if (!-r "$root/.git") {
    $Self->skip("Not in a git repository");
} else {
    my $cmd = "cd $root && nodist/spdiff . $ENV{SYSTEMPERL}";
    my $grep = `$cmd`;
    print "$grep\n";
    if ($grep ne "") {
	$Self->error("Include mismatches SystemPerl src\n");
    }
}

ok(1);
1;
