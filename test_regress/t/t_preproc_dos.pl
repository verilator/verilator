#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2006-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

top_filename("$Self->{obj_dir}/$Self->{name}.v");
$Self->{golden_filename} = "$Self->{obj_dir}/$Self->{name}.out";

# Rather then having to maintain a new .v and .out, simply add returns
# to all lines of the existing t_preproc test.

{
    my $wholefile = file_contents("$Self->{t_dir}/t_preproc.v");
    $wholefile =~ s/\n/\r\n/og;
    write_wholefile("$Self->{obj_dir}/$Self->{name}.v", $wholefile);
}
{
    my $wholefile = file_contents("$Self->{t_dir}/t_preproc.out");
    $wholefile =~ s!t/t_preproc.v!$Self->{obj_dir}/t_preproc_dos.v!og;  # Fix `line's
    write_wholefile($Self->{golden_filename}, $wholefile);
}

do 't/t_preproc.pl';

1;
