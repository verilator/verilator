#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

use IO::File;

my $root = "..";
my $Debug;

if (!-r "$root/.git") {
    $Self->skip("Not in a git repository");
} else {
    uint();
    printfll();
}

ok(1);

sub uint {
    ### Must trim output before and after our file list
    #my $files = "*/*.c* */*.h test_regress/t/*.c* test_regress/t/*.h";
    # src isn't clean, and probably doesn't need to be (yet?)
    my $files = "include/*.c* include/*.h test_c/*.c* test_regress/t/*.c* test_regress/t/*.h";
    my $cmd = "cd $root && fgrep -n int $files | sort";
    print "C $cmd\n";
    my $grep = `$cmd`;
    my %names;
    foreach my $line (split /\n/, $grep) {
	$line =~ s!//.*$!!;
	next if $line !~ /uint\d+_t\b/;
	next if $line =~ /vl[su]int\d+_t/;
	next if $line =~ /typedef/;
	next if $line =~ m!include/svdpi.h!;  # Not ours
	if ($line =~ /^([^:]+)/) {
	    $names{$1} = 1;
	    print "$line\n";
	}
    }
    if (keys %names) {
	$Self->error("Files with uint32*_t instead of vluint32s: ",join(' ',sort keys %names));
    }
}

sub printfll {
    my $files = "src/*.c* src/*.h include/*.c* include/*.h test_c/*.c* test_regress/t/*.c* test_regress/t/*.h";
    my $cmd = "cd $root && fgrep -n ll $files | sort";
    print "C $cmd\n";
    my $grep = `$cmd`;
    my %names;
    foreach my $line (split /\n/, $grep) {
	next if $line !~ /%[^ ]*ll/;
	if ($line =~ /^([^:]+)/) {
	    $names{$1} = 1;
	    print "$line\n";
	}
    }
    if (keys %names) {
	$Self->error("Files with %ll instead of VL_PRI64: ",join(' ',sort keys %names));
    }
}

1;
