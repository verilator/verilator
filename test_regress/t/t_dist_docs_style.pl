#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Primitive C++ style checker
#
# Copyright 2022 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(dist => 1);

my $root = "..";

### Must trim output before and after our file list
my %files = %{get_source_files($root)};

foreach my $file (sort keys %files) {
    my $filename = "$root/$file";
    next if !-f $filename;  # git file might be deleted but not yet staged
    next unless $file =~ /\.rst$/;

    my $contents = file_contents($filename);

    checkPattern($filename, $contents,
                 qr/.*[a-z](?<!:ref):\`[^`]+\n/,
                 "tag:`...` should not be split between lines");
}

ok(1);
1;

sub get_source_files {
    my $root = shift;
    my $git_files = `cd $root && git ls-files`;
    print "MF $git_files\n" if $Self->{verbose};
    my %files;
    foreach my $file (split /\s+/, $git_files) {
        next if $file eq '';
        $files{$file} |= 1;
    }
    return \%files;
}

sub checkPattern {
    my $filename = shift;
    my $contents = shift;
    my $pattern = shift;
    my $message = shift;

    my $offset = 0;
    my $buffer = $contents;
    while ($buffer =~ s/.*?^($pattern)//sm) {
        my $lineno = offset_to_lineno($contents, $offset + $-[-1]);
        $offset += $+[1];
        error("$filename:$lineno: $message");
    }
}

sub offset_to_lineno {
    my $contents = shift;
    my $offset = shift;
    my $count = (substr $contents, 0, $offset) =~ tr/\n//;
    return $count + 1;
}
