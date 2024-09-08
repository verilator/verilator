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
    test.compile(nc_flags2=["+ncdpiimpheader+" + test.obj_dir + "/dpi-imp.h"])

test.compile(
    v_flags2=["t/t_dpi_open_query.cpp"],
    verilator_flags2=["-Wall -Wno-DECLFILENAME"],
    # NC: Gdd the obj_dir to the C include path
    nc_flags2=["+ncscargs+-I" + test.obj_dir],
    # ModelSim: Generate DPI header, add obj_dir to the C include path
    ms_flags2=["-dpiheader " + test.obj_dir + "/dpi.h", "-ccflags -I" + test.obj_dir])

test.execute()

test.passes()
