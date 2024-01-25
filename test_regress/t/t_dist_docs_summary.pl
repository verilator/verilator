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

my @Waivers =
    (
     '+verilator+prof+threads+file+',  # Deprecated
     '+verilator+prof+threads+start+',  # Deprecated
     '+verilator+prof+threads+window+',  # Deprecated
     '-fno-',  # Documented differently
     '-no-lineno',  # Deprecated
     '-no-order-clock-delay',  # Deprecated
     '-prof-threads',  # Deprecated
    );

my %sums = %{get_summary_opts($root)};
my %docs = %{get_docs_opts($root)};

my %both = (%sums, %docs);
my %waiver = map { $_ => 1; } @Waivers;
foreach my $opt (sort keys %both) {
    next if $waiver{$opt};
    my $sum_ok = 0;
    my $docs_ok = 0;
    for my $alt (alt_names($opt)) {
        $sum_ok = 1 if $sums{$alt};
        print "$sum_ok SAC '$opt' -> '$alt'\n" if $Self->{verbose};
    }
    $sum_ok = 1 if $opt =~ /-fno-/;  # Minimal-documented optimization option
    for my $alt (alt_names($opt)) {
        $docs_ok = 1 if $docs{$alt};
        print "$sum_ok DAC '$opt' -> '$alt'\n" if $Self->{verbose};
    }
    if (!$sum_ok) {
        error($docs{$opt}.": Option documented in docs/guide '$opt'"
              ." not found in bin/* ARGUMENT SUMMARY documentation");
    } elsif (!$docs_ok) {
        error($sums{$opt}.": Option documented in bin/ ARGUMENT SUMMARY '$opt'"
              ." not found in docs/guide documentation");
    } else {
        print($docs{$opt}.": ok '$opt'\n") if $Self->{verbose};
    }
}

ok(1);
1;

sub get_summary_opts {
    my $root = shift;
    my %args = ();
    foreach my $file (glob "$root/bin/*") {
        my $fc = file_contents($file);
        my $on = 0;
        my $lineno = 0;
        foreach my $line (split(/\n/, $fc)) {
            ++$lineno;
            if ($line =~ /ARGUMENT SUMMARY/) {
                $on = 1;
            } elsif ($line =~ /=head1/) {
                $on = 0;
            } elsif ($on && $line =~ /^\s+([---+]+[^ ]+)/) {
                my $opt = opt_clean($1);
                print "S '$opt' $line\n" if $Self->{verbose};
                $args{$opt} = "$file:$lineno";
            } elsif ($line =~ /parser.add_argument\('([---+][^']+)'/) {
                my $opt = opt_clean($1);
                print "S '$opt' $line\n" if $Self->{verbose};
                $args{$opt} = "$file:$lineno";
            }
        }
    }
    return \%args;
}

sub get_docs_opts {
    my $root = shift;
    my %args = ();
    foreach my $file (glob "$root/docs/guide/*.rst") {
        my $fc = file_contents($file);
        my $lineno = 0;
        foreach my $line (split(/\n/, $fc)) {
            ++$lineno;
            if ($line =~ /option:: ([---+]+[^ `]+)/
                || $line =~ /:vlopt:`[^`]+ <([^>]+)>/
                || $line =~ /:vlopt:`([---+]+[^ `]+)/) {
                my $opt = opt_clean($1);
                print "D '$opt' $line\n" if $Self->{verbose};
                $args{$opt} = "$file:$lineno";
            }
        }
    }
    return \%args;
}

sub opt_clean {
    my $opt = shift;
    $opt =~ s/--/-/;
    $opt =~ s/<.*//;
    $opt =~ s/\\//;
    return $opt;
}

sub alt_names {
    my $opt = shift;
    my @opts = ($opt);
    push @opts, "-no".$opt if $opt =~ /^-/;
    push @opts, $1 if $opt =~ /^-no(-.*)/;
    return @opts;
}
