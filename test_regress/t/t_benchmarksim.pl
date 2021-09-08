#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

# Use any top file
top_filename("t/t_gen_alw.v");

init_benchmarksim();

# As an example, compile and simulate the top file with varying optimization level
my @l_opt = (1, 2, 3);

foreach my $l_opt (@l_opt) {
    compile(
        benchmarksim => 1,
        v_flags2 => ["-O$l_opt"]
        );

    execute(
        check_finished => 1,
        );
}

my $fh = IO::File->new("<" . benchmarksim_filename()) or error("Benchmark data file not found");
my $lines = 0;
while (defined(my $line = $fh->getline)) {
    if ($line =~ /^#/) { next; }
    if ($lines == 0) {
        error("Expected header but found $line") if $line ne "evals, time[s]\n";
    } else {
        my @data = grep {$_ != ""} ($line =~ /(\d*\.?\d*)/g);
        error("Expected 2 tokens on line " . $lines . " but got  " . scalar(@data)) if scalar(@data) != 2;
        my $cycles = $data[0];
        my $time = $data[1];
        error("Invalid data on line " . $lines) if $cycles <= 0.0 || $time <= 0.0;
    }
    $lines += 1;
}
my $n_lines_expected = scalar(@l_opt) + 1;

error("Expected " . $n_lines_expected . " lines but found " . $lines)
    if int($lines) != int($n_lines_expected);

1;
ok(1);
