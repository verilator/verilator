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
my $root = "..";
# some of the files are only used in verilation
# and are only in "include" folder
my @srcfiles = grep { !/V3Const.cpp$/ } glob("$root/src/*.cpp $root/src/obj_opt/V3Const__gen.cpp");
my $clang_args = "-I$root/src/ -I$root/include/ -I$root/src/obj_opt/ -fcoroutines-ts";
# don't check symbols that starts with
my $exclude = "std::,__builtin_,__gnu_cxx";


sub run_clang_check {
    {
        my $cmd = qq{python3 -c "from clang.cindex import Index; index = Index.create(); print(\\"Clang imported\\")";};
        print "\t$cmd\n" if $::Debug;
        my $out = `$cmd`;
        if (!$out || $out !~ /Clang imported/) { skip("No libclang installed\n"); return 1; }
    }

    my $srcfiles_str = join(" ", @srcfiles);
    run(logfile => $Self->{run_log_filename},
        tee     => 1,
        cmd     => ["python3", "$root/nodist/clang_check_attributes --gh-groups=yes --terminal-format=no --verilator-root=$root --cxxflags='$clang_args' $srcfiles_str"]);

    file_grep($Self->{run_log_filename}, "Number of functions marked as MT_SAFE calling unsafe functions: 34");
}

run_clang_check();

ok(1);
1;
