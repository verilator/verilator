#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_var_pinsizes.v");

compile (
	 v_flags2 => ["-sp -pins64 --exe $Self->{t_dir}/t_var_pinsizes.cpp"],
	 make_main => 0,
	 ) if $Self->{v3};

if ($Self->{v3}) {
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_in<bool> \s+ i1;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_in<uint32_t> \s+ i8;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_in<uint32_t> \s+ i16;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_in<uint32_t> \s+ i32;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_in<uint64_t> \s+ i64;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_in<sc_bv<65>\s> \s+ i65;/x);

    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_out<bool> \s+ o1;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_out<uint32_t> \s+ o8;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_out<uint32_t> \s+ o16;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_out<uint32_t> \s+ o32;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_out<uint64_t> \s+ o64;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.sp", qr/sc_out<sc_bv<65>\s> \s+ o65;/x);
}

ok(1);
1;
