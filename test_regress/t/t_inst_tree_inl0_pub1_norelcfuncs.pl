#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_inst_tree.v");

compile(
    verilator_flags2 => ['--stats', '-Wno-DEPRECATED', '--norelative-cfuncs',
                         "$Self->{t_dir}/t_inst_tree_inl0_pub1.vlt",
                         $Self->wno_unopthreads_for_few_cores()]
    );

if ($Self->{vlt_all}) {
    # Fewer optimizations than t_inst_tree_inl0_pub1 which allows
    # relative CFuncs:
    file_grep($Self->{stats}, qr/Optimizations, Combined CFuncs\s+(\d+)/i,
              ($Self->{vltmt} ? 0 : 31));

    # Should not find any 'this->' or 'vlSelf->' except some specific cases
    my @files = `ls $Self->{obj_dir}/*.cpp`;
    foreach my $file (@files) {
        chomp $file;
        my $text = file_contents($file);
        $text =~ s/(vlSelf|this)->vlSymsp//g;
        $text =~ s/vlSelf->.* = VL_RAND_RESET.*;//g;
        $text =~ s/vlSelf->__Vm_even_cycle//g;
        $text =~ s/vlSelf->__Vm_even_cycle//g;
        $text =~ s/vlSelf->__Vm_mtaskstate_(final|\d+)//g;
        $text =~ s/vlSelf->__Vm_threadPoolp//g;
        if ($text =~ m/this->/ || $text =~ m/vlSelf->/) {
            error("$file has unexpected this-> refs when --norelative-cfuncs");
        }
    }
}

execute(
    check_finished => 1,
    expect =>
'\] (%m|.*t\.ps): Clocked
',
    );

ok(1);
1;
