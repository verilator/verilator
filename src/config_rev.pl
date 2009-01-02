#!/usr/bin/perl -w
######################################################################
#
# Copyright 2005-2009 by Wilson Snyder.
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of either the GNU General Public License or the
# Perl Artistic License.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the Perl Artistic License
# along with this module; see the file COPYING.  If not, see
# www.cpan.org
#
######################################################################

# DESCRIPTION: Query's subversion to get version number

my $dir = $ARGV[0]; defined $dir or die "%Error: No directory argument,";
chdir $dir;

my $data = `git log | head -1`;
if ($data !~ /commit\s*([a-z0-9]+)/i) {
    die "%Error: No git revision found,";
}
my $rev = $1;

$data = `git status`;
if ($data !~ /nothing to commit/i) {
    $rev .= " (mod)";
}

print "static const char* DTVERSION_rev = \"$rev\";\n";
