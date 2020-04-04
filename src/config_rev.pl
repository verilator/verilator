#!/usr/bin/env perl
######################################################################
#
# Copyright 2005-2020 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
######################################################################
# DESCRIPTION: Query's subversion to get version number

use warnings;

my $dir = $ARGV[0]; defined $dir or die "%Error: No directory argument,";
chdir $dir;

my $rev = 'UNKNOWN_REV';
my $data = `git describe`;
if ($data =~ /^(v[0-9].*)/i) {
    $rev = $1;
}
elsif ($data =~ /verilator_?(.*)/i) {
    $rev = "v".$1;
    $rev =~ s/_/./g;
}

$data = `git status`;
if ($data =~ /Changed but not updated/i
    || $data =~ /Changes to be committed/i
    || $data =~ /Changes not staged/i) {
    $rev .= " (mod)";
}

print "static const char* const DTVERSION_rev = \"$rev\";\n";

# Die after the print, so at least the header has good contents
$rev =~ /UNKNOWN/ and warn "%Warning: No git revision found,";
