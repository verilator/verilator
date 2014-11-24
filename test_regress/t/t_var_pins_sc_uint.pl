#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

top_filename("t/t_var_pinsizes.v");

compile (
	 verilator_flags2 => ["-sc --pins-sc-uint --trace --exe $Self->{t_dir}/t_var_pinsizes.cpp"],
	 make_main => 0,
	 );

if ($Self->{vlt}) {
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<bool> \s+ i1;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<sc_uint<8>\s> \s+ i8;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<sc_uint<16>\s> \s+ i16;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<sc_uint<32>\s> \s+ i32;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<sc_uint<64>\s> \s+ i64;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<sc_bv<65>\s> \s+ i65;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<sc_bv<128>\s> \s+ i128;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<sc_bv<513>\s> \s+ i513;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<sc_bv<1>\s> \s+ ibv1;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<sc_bv<16>\s> \s+ ibv16;/x);

    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<bool> \s+ o1;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<sc_uint<8>\s> \s+ o8;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<sc_uint<16>\s> \s+ o16;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<sc_uint<32>\s> \s+ o32;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<sc_uint<64>\s> \s+ o64;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<sc_bv<65>\s> \s+ o65;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<sc_bv<128>\s> \s+ o128;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<sc_bv<513>\s> \s+ o513;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<sc_bv<1>\s> \s+ obv1;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<sc_bv<16>\s> \s+ obv16;/x);
}

execute();

ok(1);
1;
