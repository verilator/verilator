#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Hacky import order checker, used to ensure all getters
# come before setters for consistent codegen when using autocxx (#5182)
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
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
    next unless $file =~ /include.*verilated.*\.[ch].*$/;
    next if $file =~ /gtkwave/;

    my $contents = file_contents($filename);
    my %seen_setters;
    my %seen_getters;
    foreach my $line (split(/\n/, $contents . "\n\n")) {
        next if $line =~ /^\s*\/\//; # skip commented lines
        if ($line =~ /\s*void\s+([a-zA-Z0-9_]+)\([a-zA-Z0-9_]+.*/) {
            my $setter_name = $1;
            $seen_setters{$setter_name} = 1;
        } else {
            next unless $line =~ /\s*[a-zA-Z0-9_]+\s+([a-zA-Z0-9_]+)\(\s*\)/;
            my $getter_name = $1;
            if ($file =~ /verilated_sc_trace/ and $getter_name == "cycle") {
                next;  # hardcoded check for cycle() which looks like a setter but isn't
            }
            if (exists $seen_setters{$getter_name} and not (exists $seen_getters{$getter_name})) {
                error("$file: '$getter_name()' came after its setter; suggest swap order");
            }
            $seen_getters{$getter_name} = 1;
        }
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
