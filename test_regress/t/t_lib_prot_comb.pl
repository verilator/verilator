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
    xsim => 1,
    );

$Self->{sim_time} = $Self->{benchmark} * 100 if $Self->{benchmark};

my $secret_prefix = "secret";
my $secret_dir = "$Self->{obj_dir}/$secret_prefix";
mkdir $secret_dir;

while (1) {
    # Always compile the secret file with Verilator no matter what simulator
    #   we are testing with
    run(logfile => "$secret_dir/vlt_compile.log",
        cmd => ["perl",
                "$ENV{VERILATOR_ROOT}/bin/verilator",
                "--prefix",
                "Vt_lib_prot_secret",
                "-cc",
                "-Mdir",
                $secret_dir,
                "--protect-lib",
                $secret_prefix,
                "--protect-key",
                "secret-key",
                "t/t_lib_prot_comb.v"],
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
                             "+define+PROCESS_TOP",
                             "-LDFLAGS",
                             "$secret_prefix/libsecret.a"],
        xsim_flags2 => ["$secret_dir/secret.sv"],
        );

    execute(
        check_finished => 1,
        xsim_run_flags2 => ["--sv_lib",
                            "$secret_dir/libsecret",
                            "--dpi_absolute"],
        );

    ok(1);
    last;
}
1;
