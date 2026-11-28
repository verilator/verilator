#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

# This VL_API_IMPORT conflicts with VL_API_EXPORT, so the model fails to compile
# if it declares a DPI export as an import, as with dllimport and dllexport on Windows
test.compile(v_flags2=[test.pli_filename],
             verilator_flags2=[
                 "-CFLAGS -Werror=attributes",
                 "-CFLAGS \"'-DVL_API_EXPORT=__attribute__((visibility(\\\"default\\\")))'\"",
                 "-CFLAGS \"'-DVL_API_IMPORT=__attribute__((visibility(\\\"hidden\\\")))'\""
             ])

test.files_identical(test.obj_dir + "/" + test.vm_prefix + "__Dpi.h",
                     "t/" + test.name + "__Dpi.out")

test.extract(in_filename="t/" + test.name + "__Dpi.out",
             out_filename=test.root + "/docs/gen/ex_DPISTRUCT_hdr.rst",
             lines="46-56")

test.execute()

test.passes()
