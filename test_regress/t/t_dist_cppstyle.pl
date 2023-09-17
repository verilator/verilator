#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Primitive C++ style checker
#
# Copyright 2022 by Geza Lore. This program is free software; you
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
    next unless $file =~ /\.(h|c|cpp)(\.in)?$/;
    next if $file =~ /gtkwave/;

    my $contents = file_contents($filename);

    checkPattern($filename, $contents,
                 qr/[^\/]*virtual[^{};]+override/,
                 "'virtual' keyword is redundant on 'override' method");

    checkPattern($filename, $contents,
                 qr/    \s*(\w+ )*\s*(inline) [^;]+?\([^;]*?\)[^;]+?(?:{|:|=\s*default)/,
                 "'inline' keyword is redundant on method definitions inside classes");

    checkPattern($filename, $contents,
                 qr/(?<!template <>\n)inline \S+ [^;:(]+::[^;:(]+\([^;]*\)[^;]+{/,
                 "Use 'inline' only on declaration inside classes (except for template specializatoins)");

    if ($file =~ /\.(c|cpp)/) {
        checkPattern($filename, $contents,
                     qr/(\w+\s+)*(inline)/,
                     "'inline' keyword is on functions defined in .cpp files");
    }
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

    my $lineno = 0;
    my $buffer;
    foreach my $line (split(/\n/, $contents . "\n\n")) {
        ++$lineno;
        if ($line ne "") {
            # Don't do whole file at once - see issue #4085
            # Build a buffer until a newline so we check a block at a time.
            $buffer .= $line . "\n";
            next;
        }
        if ($buffer =~ s/.*?^($pattern)//sm) {
            error("$filename:$lineno: $message");
        }
        $buffer = "";
    }
}
