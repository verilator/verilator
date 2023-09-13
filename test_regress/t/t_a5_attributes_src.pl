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
rerunnable(0);
my $root = "..";
if ($ENV{VERILATOR_TEST_NO_ATTRIBUTES}) {
    skip("Skipping due to VERILATOR_TEST_NO_ATTRIBUTES");
} elsif (! -e "$root/src/obj_dbg/compile_commands.json") {
    skip("compile_commands.json not found. Please install 'bear > 3.0' and rebuild Verilator.");
} else {
    check();
}
sub check {
    # some of the files are only used in Verilation
    # and are only in "include" folder
    my @srcfiles = grep { !/\/(V3Const|Vlc\w*|\w*_test|\w*_sc|\w*.yy).cpp$/ }
                   glob("$root/src/*.cpp $root/src/obj_dbg/V3Const__gen.cpp");
    my $srcfiles_str = join(" ", @srcfiles);

    sub run_clang_check {
        {
            my $cmd = qq{python3 -c "from clang.cindex import Index; index = Index.create(); print(\\"Clang imported\\")";};
            print "\t$cmd\n" if $::Debug;
            my $out = `$cmd`;
            if (!$out || $out !~ /Clang imported/) { skip("No libclang installed\n"); return 1; }
        }
        run(logfile => $Self->{run_log_filename},
            tee => 1,
            cmd => ["python3",
                    "$root/nodist/clang_check_attributes",
                    "--verilator-root=$root",
                    "--compilation-root=$root/src/obj_dbg",
                    "--compile-commands-dir=$root/src/obj_dbg",
                    "$srcfiles_str"]);

        file_grep($Self->{run_log_filename}, "Number of functions reported unsafe: 0");
    }

    run_clang_check();
}

ok(1);
1;
