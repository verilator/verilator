#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2010 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

use Cwd;

scenarios(dist => 1);

my $root = "..";
my $Debug;

if (!-r "$root/.git") {
    skip("Not in a git repository");
} else {
    my $cwd = getcwd();
    my $destdir = "$cwd/".$Self->{obj_dir};
    # Start clean
    run(cmd => ["rm -rf $destdir && mkdir -p $destdir"],
        check_finished => 0);
    # Install into temp area
    print "Install...\n";
    run(cmd => ["cd $root && make DESTDIR=$destdir install-all"],
        check_finished => 0);

    # Check we can run a test
    # Unfortunately the prefix was hardcoded in the exec at a different place,
    # so we can't do much here.
    #print "Check install...\n";

    # Uninstall
    print "Uninstall...\n";
    run(cmd => ["cd $root && make DESTDIR=$destdir uninstall"],
        check_finished => 0);

    # Check empty
    my @files;
    $finds = `find $destdir -type f -print`;
    foreach my $file (split /\n/, $finds) {
        next if $file =~ /\.status/;  # Made by driver.pl, not Verilator
        print "\tLEFT:  $file\n";
        $file =~ s!^$cwd!.!;
        push @files, $file;
    }
    if ($#files >= 0) {
        error("Uninstall missed files: ",join(' ',@files));
    }
}

ok(1);
1;
