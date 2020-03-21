#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(dist => 1);

my $root = "..";
my $Debug;

if (!-r "$root/.git") {
    skip("Not in a git repository");
} else {
    ### Must trim output before and after our file list
    my %warns;
    my $prefix;
    my $summary;
    {
        my $status = `cd $root && git ls-files -o --exclude-standard`;
        print "ST $status\n" if $Debug;
        foreach my $file (sort split /\n/, $status) {
            next if $file =~ /nodist/;
            if (_has_tabs("$root/$file")) {
                $warns{$file} = "File not in git or .gitignore (with tabs): $file";
                $summary = "Files untracked in git or .gitignore (with tabs):"
            } else {
                $warns{$file} = "File not in git or .gitignore: $file";
                $summary ||= "Files untracked in git or .gitignore:"
            }
        }
    }
    if (keys %warns) {
        # First warning lists everything as that's shown in the driver summary
        error($summary." ",join(' ',sort keys %warns));
        foreach my $file (sort keys %warns) {
            error($warns{$file});
        }
    }
}

sub _has_tabs {
    my $filename = shift;
    my $contents = file_contents($filename);
    if ($filename =~ /\.out$/) {
        # Ignore golden files
    } elsif ($contents =~ /[\001\002\003\004\005\006]/) {
        # Ignore binrary files
    } elsif ($contents =~ /\t/) {
        return 1;
    }
    return 0;
}

ok(1);
1;
