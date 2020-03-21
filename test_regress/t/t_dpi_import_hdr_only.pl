#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Todd Strader. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

use File::Temp;
use File::Compare;

scenarios(simulator => 1);

top_filename("t/t_dpi_import.v");

my $tmp_dir = File::Temp->newdir();

compile(
    # Override default flags also
    verilator_flags => ["-Wall -Wno-DECLFILENAME -Mdir " . $tmp_dir . " --dpi-hdr-only"],
    verilator_make_gmake => 0,
    );

my @files = glob($tmp_dir . "/*");

error("Did not produce DPI header") if scalar(@files) == 0;
error("Too many files created:".join(', ', @files)) if scalar(@files) > 1;

my $tmp_header = $files[0];
print("============".$tmp_header."\n");
error("Unexpected file $tmp_header") unless $tmp_header =~ /__Dpi\.h$/;

compile(
    verilator_flags2 => ["-Wall -Wno-DECLFILENAME"],
    verilator_make_gmake => 0,
    );

@files = glob($Self->obj_dir . "/*__Dpi.h");
my $header = $files[0];

if (compare($tmp_header, $header) != 0) {
    error("DPI header files are not the same");
}

ok(1);
1;
