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
use strict;

scenarios(dist => 1);

my $root = "..";
my $Debug;
my %Files;

if (!-r "$root/.git") {
    skip("Not in a git repository");
} else {
    print "-Test is only for occasional cleanup, never completely clean\n";
    #inctree();
}

ok(1);

sub inctree {
    # Note do not do test_regress, as VPI files need to compile without verilatedos.h
    my $files = "src/*.c* src/*.h include/*.c* include/*.h";
    my $cmd = "cd $root && grep -n -P '^(# *include)' $files | sort";
    print "C $cmd\n";
    my $grep = `$cmd`;
    foreach my $line (split /\n/, $grep) {
        if ($line =~ /^(\S+):(\d+):#\s*include\s*(\S+)/) {
            my $filename = $1; my $line = $2 + 0; my $inc = $3;
            (my $base = $filename) =~ s!.*/(.*?)!$1!;
            $inc =~ s/[<>"]//g;
            $Files{$base}{filename} = $filename;
            $Files{$base}{incs}{$inc} = $line;
            #print "I $fileline   $base  $inc\n";
        } else {
            warn "%Warning: Strange line: $line\n";
        }
    }
    foreach my $base (keys %Files) {
        _inctree_recurse($base);
    }
    #use Data::Dumper; print Dumper(\%Files);
    foreach my $base (sort keys %Files) {
        my $fileref = $Files{$base};
        foreach my $subinc (sort keys %{$fileref->{incs}}) {
            my $subline = $fileref->{incs}{$subinc};
            if (my $subsubinfo = $fileref->{subincs}{$subinc}) {
                if ($subsubinfo->{line} < $subline) {
                    error("$fileref->{filename}:$subline: Include of $subinc is also included by earlier include ($subsubinfo->{name})");
                }
            }
        }
    }
}

sub _inctree_recurse {
    my $basename = shift;
    my $fileref = $Files{$basename};

    return if $fileref->{subincs};
    $fileref->{subincs} = {};
    foreach my $subinc (keys %{$fileref->{incs}}) {
        _inctree_recurse($subinc);
    }
    foreach my $subinc (keys %{$fileref->{incs}}) {
        my $subline = $fileref->{incs}{$subinc};
        foreach my $subsubinc (keys %{$Files{$subinc}{incs}}) {
            if (!$fileref->{subincs}{$subsubinc}
                || $fileref->{subincs}{$subsubinc}{line} < $subline) {
                $fileref->{subincs}{$subsubinc}
                = {line => $subline,
                   name => $subinc, };
            }
        }
    }
}

1;
