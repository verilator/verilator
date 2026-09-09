#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import glob
import re

test.scenarios('vlt')

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy --no-l2name --stats -Wno-UNOPTFLAT -Wno-UNUSED"
                 " -Wno-WIDTHTRUNC", test.pli_filename
             ])

test.execute()

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"

test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 28)
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 26)
test.file_grep(test.stats, r'VPI, lazy write-only retained\s+(\d+)', 2)
test.file_grep(test.stats, r'VPI, lazy group bail, impure\s+(\d+)', 3)
# The rotated alias pair is a comb loop, not an alias cycle.
test.file_grep(test.stats, r'VPI, lazy group bail, comb cycle\s+(\d+)', 4)
# alc_x/alc_y via u_pass1/u_pass2 is a genuine alias cycle.
test.file_grep(test.stats, r'VPI, lazy group bail, alias cycle\s+(\d+)', 6)
test.file_grep(test.stats, r'VPI, lazy group bail, cross-scope write\s+(\d+)', 2)

test.file_grep(syms, r'"rnd",.*VLVF_PUB_RW')
test.file_grep(syms, r'"crbase",.*VLVF_PUB_RW')
test.file_grep(syms, r'"rndc",.*VLVF_PUB_RW')
test.file_grep(syms, r'"tstamp",.*VLVF_PUB_RW')

for filename in glob.glob(test.obj_dir + "/*Slow*.cpp"):
    with open(filename, 'r', encoding="utf8") as fh:
        infunc = False
        for line in fh:
            if re.match(r'^\S.*__Vlazy_reconstruct__', line):
                infunc = True
            elif re.match(r'^\}', line):
                infunc = False
            elif infunc and re.search(r'VL_RANDOM|VL_TIME', line):
                test.error(filename + ": reconstruct function re-executes: " + line.strip())

test.passes()
