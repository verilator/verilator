#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

if test.nc:
    # For NC, compile twice, first just to generate DPI headers
    test.compile(nc_flags2=[
        "+ncdpiheader+" + test.obj_dir + "/dpi-exp.h", "+ncdpiimpheader+" + test.obj_dir +
        "/dpi-imp.h"
    ])

test.compile(
    v_flags2=["t/" + test.name + ".cpp"],
    # --no-decoration so .out file doesn't comment on source lines
    verilator_flags2=["-Wall -Wno-DECLFILENAME --no-decoration"],
    # NC: Gdd the obj_dir to the C include path
    nc_flags2=["+ncscargs+-I" + test.obj_dir],
    # ModelSim: Generate DPI header, add obj_dir to the C include path
    ms_flags2=["-dpiheader " + test.obj_dir + "/dpi.h", "-ccflags -I" + test.obj_dir])

if test.vlt_all:
    test.files_identical(test.obj_dir + "/" + test.vm_prefix + "__Dpi.h",
                         "t/" + test.name + "__Dpi.out")

test.execute()

test.passes()
