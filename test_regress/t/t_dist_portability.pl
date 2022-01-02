#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

use IO::File;

scenarios(dist => 1);

my $root = "..";
my $Debug;

if (!-r "$root/.git") {
    skip("Not in a git repository");
} else {
    printfll();
    cstr();
    vsnprintf();
    final();
}

ok(1);

sub printfll {
    my $files = "src/*.c* src/*.h include/*.c* include/*.h examples/*/*.c* test_regress/t/*.c* test_regress/t/*.h";
    my $cmd = "cd $root && fgrep -n ll $files | sort";
    print "C $cmd\n";
    my $grep = `$cmd`;
    my %names;
    foreach my $line (split /\n/, $grep) {
        next if $line !~ /%[a-z0-9]*ll/;
        next if $line !~ /\blong\S+long\b/;  # Assume a cast
        print "$line\n";
        if ($line =~ /^([^:]+)/) {
            $names{$1} = 1;
        } else {
            $names{UNKNOWN} = 1;
        }
    }
    if (keys %names) {
        error("Files with %ll instead of PRIx64: ", join(' ', sort keys %names));
    }
}

sub cstr {
    my $files = "src/*.c* src/*.h include/*.c* include/*.h examples/*/*.c* test_regress/t/*.c* test_regress/t/*.h";
    my $cmd = "cd $root && grep -n -P 'c_str|begin|end' $files | sort";
    print "C $cmd\n";
    my $grep = `$cmd`;
    my %names;
    foreach my $line (split /\n/, $grep) {
        if ($line =~ /^([^:]+)[^"]*\(\)[a-z0-9_().->]*[.->]+(c_str|r?begin|r?end)\(\)/) {
            next if $line =~ /lintok-begin-on-ref/;
            print "$line\n";
            $names{$1} = 1;
        }
    }
    if (keys %names) {
        error("Files with potential c_str() lifetime issue: ", join(' ', sort keys %names));
    }
}

sub vsnprintf {
    # Note do not do test_regress, as VPI files need to compile without verilatedos.h
    my $files = "src/*.c* src/*.h include/*.c* include/*.h examples/*/*.c*";
    my $cmd = "cd $root && grep -n -P '(snprintf|vsnprintf)' $files | sort";
    print "C $cmd\n";
    my $grep = `$cmd`;
    my %names;
    foreach my $line (split /\n/, $grep) {
        if ($line =~ /\b(snprintf|vsnprintf)\b/) {
            next if $line =~ /# *define\s*VL_V?SNPRINTF/;
            print "$line\n";
            $names{$1} = 1;
        }
    }
    if (keys %names) {
        error("Files with vsnprintf, use VL_VSNPRINTF: ", join(' ', sort keys %names));
    }
}

sub final {
    # Note do not do test_regress, as VPI files need to compile without verilatedos.h
    my $files = "src/*.c* src/*.h include/*.c* include/*.h";
    my $cmd = "cd $root && grep -n -P '(class)' $files | sort";
    print "C $cmd\n";
    my $grep = `$cmd`;
    my %names;
    foreach my $line (split /\n/, $grep) {
        if ($line =~ /:\s*class /) {
            next if $line =~ /final|VL_NOT_FINAL/;
            next if $line =~ /{}/;  # e.g. 'class Foo {};'
            next if $line =~ /;/;  # e.g. 'class Foo;'
            print "$line\n";
            $names{$1} = 1;
        }
    }
    if (keys %names) {
        error("Files with classes without final/VL_NOT_FINAL: ", join(' ', sort keys %names));
    }
}

1;
