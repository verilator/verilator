#!/usr/bin/perl -w
#$Id$
######################################################################
#
# Copyright 2005-2006 by Wilson Snyder.
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

my $data = `svn info`;
if ($data !~ /\nRevision:\s*(\d+)/) {
    die "%Error: No svn info revision found,";
}
my $rev = $1;
print "static int DTVERSION_rev = $rev;\n";
