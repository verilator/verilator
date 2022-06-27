#!/usr/bin/env perl
# Makes the test run with tracing enabled by default, can be overridden
# with --notrace
unshift(@ARGV, "--trace");
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Todd Strader. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(
    vlt => 1,
    vltmt => 1,
    xsim => 1,
    );
top_filename("t/t_lib_prot.v");

$Self->{sim_time} = $Self->{benchmark} * 100 if $Self->{benchmark};

my $secret_prefix = "secret";
my $secret_dir = "$Self->{obj_dir}/$secret_prefix";
my $abs_secret_dir = File::Spec->rel2abs($secret_dir);
mkdir $secret_dir;

while (1) {
    # Always compile the secret file with Verilator no matter what simulator
    #   we are testing with
    run(logfile => "$secret_dir/vlt_compile.log",
        cmd => ["perl",
                "$ENV{VERILATOR_ROOT}/bin/verilator",
                ($Self->{vltmt} ? ' --threads 6' : ''),
                "--prefix",
                "Vt_lib_prot_secret",
                "-cc",
                "-Mdir",
                $secret_dir,
                "--protect-lib",
                $secret_prefix,
                "--protect-key",
                "secret-key",
                "t/t_lib_prot_secret.v"],
        verilator_run => 1,
        );
    last if $Self->{errors};

    run(logfile => "$secret_dir/secret_gcc.log",
        cmd=>[$ENV{MAKE},
              "-C",
              $secret_dir,
              "-f",
              "Vt_lib_prot_secret.mk"]);
    last if $Self->{errors};

    compile(
        verilator_flags2 => ["$secret_dir/secret.sv",
                             "-LDFLAGS",
                             "'-Wl,-rpath,$abs_secret_dir -L$abs_secret_dir -l$secret_prefix'"],
        xsim_flags2 => ["$secret_dir/secret.sv"],
        threads => $Self->{vltmt} ? 1 : 0,
        context_threads => $Self->{vltmt} ? 6 : 1
        );

    execute(
        check_finished => 1,
        run_env => "DYLD_FALLBACK_LIBRARY_PATH=$abs_secret_dir",
        xsim_run_flags2 => ["--sv_lib",
                            "$secret_dir/libsecret",
                            "--dpi_absolute"],
        );

    if ($Self->{vlt} && $Self->{trace}) {
        # We can see the ports of the secret module
        file_grep("$Self->{obj_dir}/simx.vcd", qr/accum_in/);
        # but we can't see what's inside
        file_grep_not("$Self->{obj_dir}/simx.vcd", qr/secret_/);
    }

    ok(1);
    last;
}
1;
