#!/usr/bin/perl -w
######################################################################
#
# Copyright 2005-2015 by Wilson Snyder.  Verilator is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
######################################################################

# DESCRIPTION: Query's subversion to get version number

my $dir = $ARGV[0]; defined $dir or die "%Error: No directory argument,";
chdir $dir;

my $rev = 'UNKNOWN_REV';
my $data = `git describe`;
if ($data =~ /(verilator.*)/i) {
    $rev = $1;
}

$data = `git status`;
if ($data =~ /Changed but not updated/i
    || $data =~ /Changes to be committed/i) {
    $rev .= " (mod)";
}

print "static const char* DTVERSION_rev = \"$rev\";\n";

# Die after the print, so at least the header has good contents
$rev =~ /UNKNOWN/ and warn "%Warning: No git revision found,";
