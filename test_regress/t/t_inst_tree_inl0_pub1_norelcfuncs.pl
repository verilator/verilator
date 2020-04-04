#!/usr/bin/perl
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
    verilator_flags2 => ['--stats', '--norelative-cfuncs',
                         "$Self->{t_dir}/t_inst_tree_inl0_pub1.vlt",
                         $Self->wno_unopthreads_for_few_cores()]
    );

if ($Self->{vlt_all}) {
    # Fewer optimizations than t_inst_tree_inl0_pub1 which allows
    # relative CFuncs:
    file_grep($Self->{stats}, qr/Optimizations, Combined CFuncs\s+(\d+)/i,
              ($Self->{vltmt} ? 0 : 31));

    # Should not find any 'this->' except some 'this->__VlSymsp'
    my @files = `ls $Self->{obj_dir}/*.cpp`;
    foreach my $file (@files) {
        chomp $file;
        my $text = file_contents($file);
        $text =~ s/this->__VlSymsp//g;
        if ($text =~ m/this->/) {
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
