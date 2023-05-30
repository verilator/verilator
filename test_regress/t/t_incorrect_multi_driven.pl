#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }

scenarios(linter => 1);

top_filename("t/t_incorrect_multi_driven.v");

lint(
    fails => 0
    );

ok(1);
1;
