#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

# This test makes sure that the intenral check of t_hier_block.v is correct.
# --hierarchical option is not set intentionally.

# stats will be deleted but generation will be skipped if libs of hierarchical blocks exist.
clean_objs();

scenarios(vlt_all => 1);
top_filename("t/t_hier_block.v");

# CI environment offers 2 VCPUs, 2 thread setting causes the following warning.
# %Warning-UNOPTTHREADS: Thread scheduler is unable to provide requested parallelism; consider asking for fewer threads.
# So use 6 threads here though it's not optimal in performace wise, but ok.
compile(
    v_flags2 => ['t/t_hier_block.cpp'],
    verilator_flags2 => ['--stats',
                         '+define+USE_VLT', 't/t_hier_block_vlt.vlt',
                         '--CFLAGS', '"-pipe -DCPP_MACRO=cplusplus"'],
    threads => $Self->{vltmt} ? 6 : 0
    );

execute(
    check_finished => 1,
    );

file_grep_not($Self->{stats}, qr/HierBlock,\s+Hierarchical blocks\s+(\d+)/i);
file_grep($Self->{run_log_filename}, qr/MACRO:(\S+) is defined/i, "cplusplus");

ok(1);
1;
