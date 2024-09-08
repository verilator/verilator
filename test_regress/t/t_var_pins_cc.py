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
test.top_filename = "t/t_var_pinsizes.v"

test.compile(verilator_flags2=['-cc'],
             verilator_make_gmake=False,
             make_top_shell=False,
             make_main=False)


def hgrep(re):
    test.file_grep(os.path.join(test.obj_dir, test.vm_prefix + ".h"), re)


hgrep(r'VL_IN8\(&i1,0,0\);')
hgrep(r'VL_IN8\(&i8,7,0\);')
hgrep(r'VL_IN16\(&i16,15,0\);')
hgrep(r'VL_IN\(&i32,31,0\);')
hgrep(r'VL_IN64\(&i64,63,0\);')
hgrep(r'VL_INW\(&i65,64,0,3\);')

hgrep(r'VL_OUT8\(&o1,0,0\);')
hgrep(r'VL_OUT8\(&o8,7,0\);')
hgrep(r'VL_OUT16\(&o16,15,0\);')
hgrep(r'VL_OUT\(&o32,31,0\);')
hgrep(r'VL_OUT64\(&o64,63,0\);')
hgrep(r'VL_OUTW\(&o65,64,0,3\);')

test.passes()
