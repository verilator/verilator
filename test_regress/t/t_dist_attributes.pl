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
my $input_dirs = "$root/src $root/src/obj_opt $root/include";
my $include_dirs = "-I$root/src/ -I$root/include/ -I$root/include/vltstd/ -I$root/src/obj_opt/ -fcoroutines-ts";
# don't check symbols that starts with
my $exclude = "std::,__builtin_,__gnu_cxx";


sub run_clang_check {
    {
        my $cmd = qq{python3 -c "import clang.cindex; print(clang.cindex.conf.get_filename())";};
        print "\t$cmd\n" if $::Debug;
        my $out = `$cmd`;
        if (!$out || $out !~ /libclang/) { skip("No libclang installed\n"); return 1; }
    }
    my $stdout_filename = "$Self->{obj_dir}/clang_check_attributes.log";
    run(logfile => $stdout_filename,
        tee     => 1,
        cmd     => ["python3", "$root/nodist/clang_check_attributes.py $input_dirs $include_dirs -x $exclude"]);
    files_identical($stdout_filename, $Self->{golden_filename});
}

run_clang_check();

ok(1);
1;
