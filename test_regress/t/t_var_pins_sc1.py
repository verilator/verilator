#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.pli_filename = "t/t_var_pinsizes.cpp"
test.top_filename = "t/t_var_pinsizes.v"

test.compile(verilator_flags2=[
    "-sc -pins-bv 1 --trace --exe", test.pli_filename, test.t_dir + "/t_var_pinsizes.vlt"
],
             make_main=False)


def hgrep(re):
    test.file_grep(os.path.join(test.obj_dir, test.vm_prefix + ".h"), re)


hgrep(r'sc_core::sc_in<sc_dt::sc_bv<1>\s>\s+&i1;')
hgrep(r'sc_core::sc_in<sc_dt::sc_bv<8>\s>\s+&i8;')
hgrep(r'sc_core::sc_in<sc_dt::sc_bv<16>\s>\s+&i16;')
hgrep(r'sc_core::sc_in<sc_dt::sc_bv<32>\s>\s+&i32;')
hgrep(r'sc_core::sc_in<sc_dt::sc_bv<64>\s>\s+&i64;')
hgrep(r'sc_core::sc_in<sc_dt::sc_bv<65>\s>\s+&i65;')
hgrep(r'sc_core::sc_in<sc_dt::sc_bv<1>\s>\s+&ibv1;')
hgrep(r'sc_core::sc_in<sc_dt::sc_bv<16>\s>\s+&ibv16;')
hgrep(r'sc_core::sc_in<sc_dt::sc_bv<1>\s>\s+&ibv1_vlt;')
hgrep(r'sc_core::sc_in<sc_dt::sc_bv<16>\s>\s+&ibv16_vlt;')

hgrep(r'sc_core::sc_out<sc_dt::sc_bv<1>\s>\s+&o1;')
hgrep(r'sc_core::sc_out<sc_dt::sc_bv<8>\s>\s+&o8;')
hgrep(r'sc_core::sc_out<sc_dt::sc_bv<16>\s>\s+&o16;')
hgrep(r'sc_core::sc_out<sc_dt::sc_bv<32>\s>\s+&o32;')
hgrep(r'sc_core::sc_out<sc_dt::sc_bv<64>\s>\s+&o64;')
hgrep(r'sc_core::sc_out<sc_dt::sc_bv<65>\s>\s+&o65;')
hgrep(r'sc_core::sc_out<sc_dt::sc_bv<1>\s>\s+&obv1;')
hgrep(r'sc_core::sc_out<sc_dt::sc_bv<16>\s>\s+&obv16;')
hgrep(r'sc_core::sc_out<sc_dt::sc_bv<1>\s>\s+&obv1_vlt;')
hgrep(r'sc_core::sc_out<sc_dt::sc_bv<16>\s>\s+&obv16_vlt;')

test.execute()

test.passes()
