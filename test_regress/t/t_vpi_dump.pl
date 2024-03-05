#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

skip("Known compiler limitation")
    if $Self->cxx_version =~ /\(GCC\) 4.4/;

compile(
    make_top_shell => 0,
    make_main => 0,
    make_pli => 1,
    iv_flags2 => ["-g2005-sv"],
    verilator_flags2 => ["--exe --vpi --public-flat-rw --no-l2name $Self->{t_dir}/t_vpi_dump.cpp $Self->{t_dir}/TestVpiMain.cpp"],
    make_flags => 'CPPFLAGS_ADD=-DVL_NO_LEGACY',
    );

execute(
    use_libvpi => 1,
    check_finished => 1,
    expect_filename => $Self->{golden_filename},
    xrun_run_expect_filename => ($Self->{golden_filename} =~ s/\.out$/.xrun.out/r),
    iv_run_expect_filename => ($Self->{golden_filename} =~ s/\.out$/.iv.out/r),
    );

ok(1);
1;
