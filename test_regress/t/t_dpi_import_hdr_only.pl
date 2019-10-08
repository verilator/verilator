#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Todd Strader. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

use File::Temp;
use File::Compare;

scenarios(simulator => 1);

top_filename("t/t_dpi_import.v");

my $tmp_dir = File::Temp->newdir();

compile(
    verilator_flags2 => ["-Wall -Wno-DECLFILENAME -Mdir " . $tmp_dir . " --dpi-hdr-only"],
    verilator_make_gmake => 0,
    );

my @files = glob($tmp_dir . "/*");

die "Did not produce DPI header" if scalar(@files) == 0;
die "Too many files created" if scalar(@files) > 1;
my $tmp_header = $files[0];
print("============".$tmp_header."\n");
die "Unexpected file $tmp_header" unless $tmp_header =~ /__Dpi\.h$/;

compile(
    verilator_flags2 => ["-Wall -Wno-DECLFILENAME"],
    verilator_make_gmake => 0,
    );

@files = glob($Self->obj_dir . "/*__Dpi.h");
my $header = @files[0];

if (compare($tmp_header, $header) != 0) {
    die "DPI header files are not the same";
}

ok(1);
1;
