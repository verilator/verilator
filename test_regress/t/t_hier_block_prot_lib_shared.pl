#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_hier_block.v");

scenarios(vlt_all => 1, xsim => 1);

my $secret_prefix = "secret";
my $secret_dir = "$Self->{obj_dir}/$secret_prefix";
mkdir $secret_dir;
my $abs_secret_dir = File::Spec->rel2abs($secret_dir);

while (1) {
    # Always compile the secret file with Verilator no matter what simulator
    #   we are testing with
    run(logfile => "$secret_dir/vlt_compile.log",
        cmd => ["perl",
                "$ENV{VERILATOR_ROOT}/bin/verilator",
                "-cc",
                "--hierarchical",
                "-Mdir",
                $secret_dir,
                "--protect-lib",
                $secret_prefix,
                "--protect-key",
                "PROTECT_KEY",
                "t/t_hier_block.v",
                "-DAS_PROT_LIB",
                '--CFLAGS', '"-pipe -DCPP_MACRO=cplusplus"',
                $Self->{vltmt} ? ' --threads 1' : '',
                "--build"],
        verilator_run => 1,
        );
    last if $Self->{errors};

    compile(
        v_flags2 => ['t/t_hier_block.cpp'],
        verilator_flags2 => ["$secret_dir/secret.sv",
                             "-DPROTLIB_TOP",
                             "--top-module t",
                             "-LDFLAGS",
                             "'-Wl,-rpath,$abs_secret_dir -L$abs_secret_dir -l$secret_prefix'"],
        );

    execute(
        check_finished => 1,
        run_env => "DYLD_FALLBACK_LIBRARY_PATH=$abs_secret_dir"
        );


    ok(1);
    last;
}

file_grep($secret_dir . "/Vsub0/sub0.sv", /^module\s+(\S+)\s+/, "sub0");
file_grep($secret_dir . "/Vsub1/sub1.sv", /^module\s+(\S+)\s+/, "sub1");
file_grep($secret_dir . "/Vsub2/sub2.sv", /^module\s+(\S+)\s+/, "sub2");
file_grep($Self->{run_log_filename}, qr/MACRO:(\S+) is defined/i, "cplusplus");

ok(1);
1;
