#!/usr/bin/perl
# DESCRIPTION: Verilator: Verilog Test driver bootstrapper
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

# This is exec'ed by every test that is run standalone (called from the
# shell as ./t_test_name.pl)

use FindBin;
use Cwd qw(chdir);

my @args = @ARGV;
chdir("$FindBin::Bin/..");

@args = map { s!.*test_regress/!!; $_; } @args;

print "cd $ENV{PWD} && $FindBin::Bin/bootstrap.pl ",join(' ',@args),"\n";
exec("./driver.pl", @args);
die;
