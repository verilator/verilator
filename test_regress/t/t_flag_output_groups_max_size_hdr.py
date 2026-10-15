#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_flag_output_groups_max_size.v"

MAX_SIZE_BYTES = 1024 * 1024

test.compile(verilator_flags2=[
    "-GN=20000", "--unroll-limit 32768", "--output-split 1000", "--output-groups 2",
    "--output-groups-size",
    str(MAX_SIZE_BYTES)
],
             verilator_make_gmake=False)

# The generated headers alone exceed the size limit
header_bytes = sum(os.path.getsize(f) for f in test.glob_some(test.obj_dir + "/*.h"))
if header_bytes <= MAX_SIZE_BYTES:
    test.error("Headers are only " + str(header_bytes) + " bytes")

# So no files are concatenated
test.file_grep_not(test.obj_dir + "/" + test.vm_prefix + "_classes.mk", r'vm_classes_')

test.passes()
