#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2012 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

my $out_filename = "$Self->{obj_dir}/V$Self->{name}.xml";

compile (
    verilator_flags2 => ['--xml-only'],
    verilator_make_gcc => 0,
    );

ok(files_identical("$out_filename", "t/$Self->{name}.out"));

1;
