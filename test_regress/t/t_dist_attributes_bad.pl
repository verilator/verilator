#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2022 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

use Cwd qw(abs_path);
use JSON::PP;
use IO::File;

scenarios(dist => 1);

my $root = "..";

if ($ENV{VERILATOR_TEST_NO_ATTRIBUTES}) {
    skip("Skipping due to VERILATOR_TEST_NO_ATTRIBUTES");
} elsif (!-r "$root/.git") {
    skip("Not in a git repository");
} else {
    check();
}

sub gen_compile_commands_json {
    my $json = JSON::PP->new->utf8->pretty;
    $json->canonical();  # Sort hash keys on ouptut

    my $root_dir = abs_path("..");
    my $srcs_dir = abs_path("./t/t_dist_attributes");
    my @common_args = ("clang++",
                       "-std=c++14",
                       "-I$root_dir/include",
                       "-I$root_dir/src",
                       "-c");

    my $ccjson = [
        {"directory" => "$srcs_dir",
         "file" => "$srcs_dir/mt_enabled.cpp",
         "output" => undef,
         "arguments" => [@common_args]},
        {"directory" => "$srcs_dir",
         "file" => "$srcs_dir/mt_disabled.cpp",
         "output" => undef,
         "arguments" => [@common_args]},
    ];

    my @srcfiles;
    foreach my $entry (@$ccjson) {
        # Add "output" key
        ($entry->{"output"} = $entry->{"file"}) =~ s/\.cpp$/.o/;
        # Add "-o src.o src.cpp" arguments
        push @{$entry->{"arguments"}}, ("-o", $entry->{"output"}, $entry->{"file"});

        push @srcfiles, $entry->{"file"};
    }

    return (
        \@srcfiles,
        $json->encode($ccjson)
    );
}

sub check {
    my $root = abs_path("..");
    my $ccjson_file = "$Self->{obj_dir}/compile_commands.json";
    my ($srcfiles, $ccjson) = gen_compile_commands_json();
    my $srcfiles_str = join(" ", @$srcfiles);
    {
        my $fh = IO::File->new(">$ccjson_file") or die "%Error: $! $ccjson_file";
        print $fh $ccjson;
        $fh->close();
    }

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
            cmd => ["python3",
                    "$root/nodist/clang_check_attributes",
                    "--verilator-root=.",
                    "--compile-commands-dir=$Self->{obj_dir}",
                    "$srcfiles_str"]);

        files_identical($Self->{run_log_filename}, $Self->{golden_filename});
    }

    run_clang_check();
}

ok(1);
1;
