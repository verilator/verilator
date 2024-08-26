#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

top_filename("t/t_var_pinsizes.v");

compile(
    verilator_flags2 => ["-sc -pins-bv 2 --trace --exe $Self->{t_dir}/t_var_pinsizes.cpp $Self->{t_dir}/t_var_pinsizes.vlt"],
    make_main => 0,
    );

{
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<bool>\s+&i1;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<sc_dt::sc_bv<8>\s>\s+&i8;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<sc_dt::sc_bv<16>\s>\s+&i16;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<sc_dt::sc_bv<32>\s>\s+&i32;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<sc_dt::sc_bv<64>\s>\s+&i64;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<sc_dt::sc_bv<65>\s>\s+&i65;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<sc_dt::sc_bv<1>\s>\s+&ibv1;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<sc_dt::sc_bv<16>\s>\s+&ibv16;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<sc_dt::sc_bv<1>\s>\s+&ibv1_vlt;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<sc_dt::sc_bv<16>\s>\s+&ibv16_vlt;/);

    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<bool>\s+&o1;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<sc_dt::sc_bv<8>\s>\s+&o8;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<sc_dt::sc_bv<16>\s>\s+&o16;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<sc_dt::sc_bv<32>\s>\s+&o32;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<sc_dt::sc_bv<64>\s>\s+&o64;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<sc_dt::sc_bv<65>\s>\s+&o65;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<sc_dt::sc_bv<1>\s>\s+&obv1;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<sc_dt::sc_bv<16>\s>\s+&obv16;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<sc_dt::sc_bv<1>\s>\s+&obv1_vlt;/);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<sc_dt::sc_bv<16>\s>\s+&obv16_vlt;/);
}

execute();

ok(1);
1;
