#!/usr/bin/perl
# This file ONLY is placed into the Public Domain, for any use,
# Author: Yu-Sheng Lin johnjohnlys@media.ee.ntu.edu.tw

if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }

scenarios(vlt_all => 1);

compile(
    v_flags2 => ["--trace-fst"],
);

execute(
    check_finished => 1,
);

fst_identical($Self->trace_filename, $Self->{golden_filename});

ok(1);
1;
