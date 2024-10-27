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

test.compile(verilator_flags2=["-sc -pins-uint8 --trace --exe", test.pli_filename],
             make_main=False)

test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h", r'sc_core::sc_in<bool>\s+&i1;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h", r'sc_core::sc_in<uint8_t>\s+&i8;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h", r'sc_core::sc_in<uint16_t>\s+&i16;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h", r'sc_core::sc_in<uint32_t>\s+&i32;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h", r'sc_core::sc_in<uint64_t>\s+&i64;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h",
               r'sc_core::sc_in<sc_dt::sc_bv<65>\s>\s+&i65;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h",
               r'sc_core::sc_in<sc_dt::sc_bv<1>\s>\s+&ibv1;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h",
               r'sc_core::sc_in<sc_dt::sc_bv<16>\s>\s+&ibv16;')

test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h", r'sc_core::sc_out<bool>\s+&o1;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h", r'sc_core::sc_out<uint8_t>\s+&o8;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h", r'sc_core::sc_out<uint16_t>\s+&o16;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h", r'sc_core::sc_out<uint32_t>\s+&o32;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h", r'sc_core::sc_out<uint64_t>\s+&o64;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h",
               r'sc_core::sc_out<sc_dt::sc_bv<65>\s>\s+&o65;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h",
               r'sc_core::sc_out<sc_dt::sc_bv<1>\s>\s+&obv1;')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + ".h",
               r'sc_core::sc_out<sc_dt::sc_bv<16>\s>\s+&obv16;')

test.execute()

test.passes()
