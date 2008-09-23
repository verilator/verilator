#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2006-2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("obj_dir/$Last_Self->{name}.v");

# Rather then having to maintain a new .v and .out, simply add returns
# to all lines of the existing t_preproc test.

$golden_out ||= "obj_dir/$Last_Self->{name}.out";

{
    my $wholefile = file_contents("t/t_preproc.v");
    $wholefile =~ s/\n/\r\n/og;
    write_wholefile("obj_dir/$Last_Self->{name}.v", $wholefile);
}
{
    my $wholefile = file_contents("t/t_preproc.out");
    $wholefile =~ s!t/t_preproc.v!obj_dir/t_preproc_dos.v!og;  # Fix `line's
    write_wholefile($golden_out, $wholefile);
}

require 't/t_preproc.pl';

1;
