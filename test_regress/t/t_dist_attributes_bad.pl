#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2022 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(dist => 1);
if ($ENV{VERILATOR_TEST_NO_ATTRIBUTES}) {
    skip("Skipping due to VERILATOR_TEST_NO_ATTRIBUTES");
} else {
    check();
}
sub check {
    my $root = "..";
    my @srcfiles = glob("$root/test_regress/t/t_dist_attributes_bad.cpp");
    my $srcfiles_str = join(" ", @srcfiles);
    my $clang_args = "-I$root/include";

    sub run_clang_check {
        {
            my $cmd = qq{python3 -c "from clang.cindex import Index; index = Index.create(); print(\\"Clang imported\\")";};
            print "\t$cmd\n" if $::Debug;
            my $out = `$cmd`;
            if (!$out || $out !~ /Clang imported/) { skip("No libclang installed\n"); return 1; }
        }
        run(logfile => $Self->{run_log_filename},
            tee => 1,
            # With `--verilator-root` set to the current directory
            # (i.e. `test_regress`) the script will skip annotation issues in
            # headers from the `../include` directory.
            cmd => ["python3", "$root/nodist/clang_check_attributes --verilator-root=. --cxxflags='$clang_args' $srcfiles_str"]);

        files_identical($Self->{run_log_filename}, $Self->{golden_filename});
    }

    run_clang_check();
}

ok(1);
1;
