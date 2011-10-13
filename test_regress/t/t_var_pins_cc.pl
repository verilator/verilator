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
	 verilator_flags2 => ['-cc'],
	 verilator_make_gcc => 0,
	 );

if ($Self->{vlt}) {
    file_grep ("$Self->{obj_dir}/Vt_var_pins_cc.h", qr/VL_IN8  \(i1,0,0\);/x);
    file_grep ("$Self->{obj_dir}/Vt_var_pins_cc.h", qr/VL_IN8  \(i8,7,0\);/x);
    file_grep ("$Self->{obj_dir}/Vt_var_pins_cc.h", qr/VL_IN16 \(i16,15,0\);/x);
    file_grep ("$Self->{obj_dir}/Vt_var_pins_cc.h", qr/VL_IN   \(i32,31,0\);/x);
    file_grep ("$Self->{obj_dir}/Vt_var_pins_cc.h", qr/VL_IN64 \(i64,63,0\);/x);
    file_grep ("$Self->{obj_dir}/Vt_var_pins_cc.h", qr/VL_INW  \(i65,64,0,3\);/x);

    file_grep ("$Self->{obj_dir}/Vt_var_pins_cc.h", qr/VL_OUT8 \(o1,0,0\);/x);
    file_grep ("$Self->{obj_dir}/Vt_var_pins_cc.h", qr/VL_OUT8 \(o8,7,0\);/x);
    file_grep ("$Self->{obj_dir}/Vt_var_pins_cc.h", qr/VL_OUT16\(o16,15,0\);/x);
    file_grep ("$Self->{obj_dir}/Vt_var_pins_cc.h", qr/VL_OUT  \(o32,31,0\);/x);
    file_grep ("$Self->{obj_dir}/Vt_var_pins_cc.h", qr/VL_OUT64\(o64,63,0\);/x);
    file_grep ("$Self->{obj_dir}/Vt_var_pins_cc.h", qr/VL_OUTW \(o65,64,0,3\);/x);
}

ok(1);
1;
