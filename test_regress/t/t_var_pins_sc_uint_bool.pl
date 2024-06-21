#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

top_filename("t/t_var_pinsizes.v");

compile(
    verilator_flags2 => ["-sc --pins-sc-uint-bool --trace --exe $Self->{t_dir}/t_var_pinsizes.cpp"],
    make_main => 0,
    );

{
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<sc_dt::sc_uint<1>\s> \s+ &i1;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<uint32_t> \s+ &i8;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<uint32_t> \s+ &i16;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<uint32_t> \s+ &i32;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<uint64_t> \s+ &i64;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<sc_dt::sc_bv<65>\s> \s+ &i65;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<sc_dt::sc_bv<128>\s> \s+ &i128;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_in<sc_dt::sc_bv<513>\s> \s+ &i513;/x);

    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<sc_dt::sc_uint<1>\s> \s+ &o1;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<uint32_t> \s+ &o8;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<uint32_t> \s+ &o16;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<uint32_t> \s+ &o32;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<uint64_t> \s+ &o64;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<sc_dt::sc_bv<65>\s> \s+ &o65;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<sc_dt::sc_bv<128>\s> \s+ &o128;/x);
    file_grep("$Self->{obj_dir}/$Self->{vm_prefix}.h", qr/sc_core::sc_out<sc_dt::sc_bv<513>\s> \s+ &o513;/x);
}

execute();

ok(1);
1;
