#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Todd Strader. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(
    vlt => 1,
    xsim => 1,
    );

# Always compile the secret file with Verilator no matter what simulator
#   we are testing with
my $cmd = ["t/t_prot_lib_secret.pl", "--vlt"];
my $secret_prefix = "t_prot_lib_secret";

my $secret_dir = "$Self->{obj_dir}/../../obj_vlt/$secret_prefix";

while (1) {
    run(logfile => "$Self->{obj_dir}/secret_compile.log",
        cmd => $cmd);
    last if $Self->{errors};

    compile(
        verilator_flags2 => ["$secret_dir/secret.sv",
                             "--trace", "-LDFLAGS",
                             "'-L../$secret_prefix -lsecret -static'"],
        xsim_flags2 => ["$secret_dir/secret.sv"],
        );

    execute(
        check_finished => 1,
        xsim_run_flags2 => ["--debug",
                            "all",
                            "--sv_lib",
                            "$secret_dir/libsecret",
                            "--dpi_absolute"],
        );

    if ($Self->{vlt}) {
        # We can see the ports of the secret module
        file_grep("$Self->{obj_dir}/simx.vcd", qr/accum_in/);
        # but we can't see what's inside
        file_grep_not("$Self->{obj_dir}/simx.vcd", qr/secret_/);
    }

    ok(1);
    last;
}
1;
