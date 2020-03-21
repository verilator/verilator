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

### Must trim output before and after our file list
my %files = %{get_manifest_files($root)};

foreach my $file (sort keys %files) {
    my $filename = "$root/$file";
    my $contents = file_contents($filename);
    if ($file =~ /\.out$/) {
        # Ignore golden files
        next;
    } elsif ($contents =~ /[\001\002\003\004\005\006]/) {
        # Ignore binary files
        next;
    }
    if ($contents !~ /\n$/s && $contents ne "") {
        $warns{$file} = "Missing trailing newline in $file";
    }
    if ($contents =~ /[ \t]\n/
        || $contents =~ m/\n\n+$/) {  # Regexp repeated below
        my $eol_ws_exempt = ($file =~ /(\.txt|\.html)$/
                             || $file =~ m!^README$!
                             || $file =~ m!/gtkwave/!);
        if ($ENV{HARNESS_UPDATE_GOLDEN}) {
            my $changes = undef;
            $changes = 1 if ($contents =~ s/[ \t]+\n/\n/g);
            $changes = 1 if (!$eol_ws_exempt && $contents =~ s/\n\n+$/\n/g);
            next if (!$changes);
            $warns{$file} = "Updated whitespace at $file";
            write_wholefile($filename, $contents);
            next;
        }
        my @lines = split(/\n/, $contents);
        my $line_no = 0;
        foreach my $line (@lines) {
            $line_no++;
            # Trim trailing carriage-return (ascii 0xd) and form feed (0xc),
            # as we expect a few of those
            $line =~ s/[\x{d}\x{c}]//g;
            if ($line =~ /\s$/) {
                $warns{$file} = "Trailing whitespace at $file:$line_no";
                $warns{$file} .= " (last character is ASCII " . ord(substr($line, -1, 1)) . ")";
            }
        }
        if ($contents =~ m/\n\n+$/ && !$eol_ws_exempt) {  # Regexp repeated above
            $warns{$file} = "Trailing newlines at EOF in $file";
        }
    }
}

if (keys %warns) {
    # First warning lists everything as that's shown in the driver summary
    if ($ENV{HARNESS_UPDATE_GOLDEN}) {
        error("Updated files with whitespace errors: ",join(' ',sort keys %warns));
        error("To auto-fix: HARNESS_UPDATE_GOLDEN=1 {command} or --golden");
    } else {
        error("Files have whitespace errors: ",join(' ',sort keys %warns));
        error("To auto-fix: HARNESS_UPDATE_GOLDEN=1 {command} or --golden");
    }
    foreach my $file (sort keys %warns) {
        error($warns{$file});
    }
}

ok(1);
1;

sub get_manifest_files {
    my $root = shift;
    `cd $root && make dist-file-list`;
    my $manifest_files = `cd $root && make dist-file-list`;
    $manifest_files =~ s!.*begin-dist-file-list:!!sg;
    $manifest_files =~ s!end-dist-file-list:.*$!!sg;
    print "MF $manifest_files\n" if $Self->{verbose};
    my %files;
    foreach my $file (split /\s+/,$manifest_files) {
        next if $file eq '';
        $files{$file} |= 1;
    }
    return \%files;
}
