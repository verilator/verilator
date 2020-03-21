#!/usr/bin/perl
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
    formats();
}

ok(1);

# Check all error messages match our standard format
# This assumes .out files cover all important errors

sub formats {
    my $files = "../test_regress/t/*.out";
    my %warns;
    my $lnmatch = 0;
    foreach my $file (glob $files) {
        my $wholefile = file_contents($file);
        $file =~ s!.*/!!;
        if ($wholefile =~ /Exiting due to/
            || $wholefile =~ /%(Error|Warning)/) {
            my $lineno = 0;
            foreach my $line (split /\n/, $wholefile) {
                ++$lineno;
                if ($line =~ /(Error|Warning)/) {
                    # These formats are documented in bin/verilator
                    # Error with fileline
                    # For testing only: we assume no : in filename
                    my $match = $line;
                    $match =~ s/^\[\d+\] //;  # Simplify runtime errors
                    if ($match =~ /^%(Error|Warning)(-[A-Z0-9_]+)?: ([^:]+):(\d+):((\d+):)? /) {
                        ++$lnmatch;
                        print "ok-el $file $line\n" if $Self->{verbose};
                    }
                    # Error no fileline
                    # For testing only: we assume any : is single quoted
                    elsif ($match =~ /^%(Error|Warning)(-[A-Z0-9_]+)?: [^:']+/) {
                        print "ok-en $file $line\n" if $Self->{verbose};
                    }
                    else {
                        #print "FF $file $line\n";
                        $warns{$file.":".$lineno} =
                            "Non-standard warning/error: $file:$lineno: $line";
                    }
                }
            }
        }
    }
    $lnmatch or error("Check line number regexp is correct, no matches");
    if (keys %warns) {
        # First warning lists everything as that's shown in the driver summary
        error($summary." ",join(' ',sort keys %warns));
        foreach my $file (sort keys %warns) {
            error($warns{$file});
        }
    }
}

1;
