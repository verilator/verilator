#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_var_pinsizes.v");

compile (
	 v_flags2 => ['-sp -pins-bv 2'],
	 verilator_make_gcc => 0,
	 ) if $Self->{v3};

if ($Self->{v3}) {
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_in<bool> \s+ i1;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_in<sc_bv<8>\s> \s+ i8;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_in<sc_bv<16>\s> \s+ i16;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_in<sc_bv<32>\s> \s+ i32;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_in<sc_bv<64>\s> \s+ i64;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_in<sc_bv<65>\s> \s+ i65;/x);

    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_out<bool> \s+ o1;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_out<sc_bv<8>\s> \s+ o8;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_out<sc_bv<16>\s> \s+ o16;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_out<sc_bv<32>\s> \s+ o32;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_out<sc_bv<64>\s> \s+ o64;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_out<sc_bv<65>\s> \s+ o65;/x);
}

ok(1);
1;
