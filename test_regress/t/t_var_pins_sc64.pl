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
	 verilator_flags2 => ["-sc -pins64 --trace --exe $Self->{t_dir}/t_var_pinsizes.cpp"],
	 make_main => 0,
	 );

if ($Self->{vlt}) {
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<bool> \s+ i1;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<uint32_t> \s+ i8;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<uint32_t> \s+ i16;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<uint32_t> \s+ i32;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<vluint64_t> \s+ i64;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<sc_bv<65>\s> \s+ i65;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<sc_bv<1>\s> \s+ ibv1;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_in<sc_bv<16>\s> \s+ ibv16;/x);

    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<bool> \s+ o1;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<uint32_t> \s+ o8;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<uint32_t> \s+ o16;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<uint32_t> \s+ o32;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<vluint64_t> \s+ o64;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<sc_bv<65>\s> \s+ o65;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<sc_bv<1>\s> \s+ obv1;/x);
    file_grep ("$Self->{obj_dir}/$Self->{VM_PREFIX}.h", qr/sc_out<sc_bv<16>\s> \s+ obv16;/x);
}

execute();

ok(1);
1;
