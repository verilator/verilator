#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import filecmp

test.scenarios('simulator')
test.top_filename = "t/t_dpi_import.v"

tmp_dir = test.obj_dir + "/dpi-hdr"
test.mkdir_ok(tmp_dir)

test.compile(
    # Override default flags also
    verilator_flags=["-Wall -Wno-DECLFILENAME -Mdir " + tmp_dir + " --dpi-hdr-only"],
    verilator_make_gmake=False)

files = glob.glob(tmp_dir + "/*")

if len(files) < 1:
    test.error("Did not produce DPI header")
if len(files) > 1:
    test.error("Too many files created:" + ', '.join(files))

tmp_header = files[0]
print("============" + tmp_header)

if not re.search(r'__Dpi\.h$', tmp_header):
    test.error("Unexpected file " + tmp_header)

test.compile(verilator_flags2=["-Wall -Wno-DECLFILENAME"], verilator_make_gmake=False)

files = glob.glob(test.obj_dir + "/*__Dpi.h")
header = files[0]

if not filecmp.cmp(tmp_header, header):
    test.error("DPI header files are not the same")

test.passes()
