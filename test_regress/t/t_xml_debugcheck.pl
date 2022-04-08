#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2012 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

my $out_filename = "$Self->{obj_dir}/V$Self->{name}.xml";

top_filename("t/t_enum_type_methods.v");

compile(
    verilator_flags2 => ['--debug-check', '--flatten'],
    verilator_make_gmake => 0,
    make_top_shell => 0,
    make_main => 0,
    );

files_identical("$out_filename", $Self->{golden_filename}, 'logfile');

# make sure that certain tags are present in --debug-check
# that would not be present in --xml-only
file_grep("$out_filename", qr/<constpool /x);
file_grep("$out_filename", qr/<inititem /x);
file_grep("$out_filename", qr/<if /x);
file_grep("$out_filename", qr/<while /x);
file_grep("$out_filename", qr/<begin>/x);  # for <if> and <while>
file_grep("$out_filename", qr/ signed=/x);  # for <basicdtype>
file_grep("$out_filename", qr/ func=/x);  # for <ccall>

ok(1);
1;
