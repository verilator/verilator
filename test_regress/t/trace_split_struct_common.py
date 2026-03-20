# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


def run(test):
    (fmt,) = test.parse_name(r"t_trace_split_struct_([a-z]+)")

    test.top_filename = "t/t_trace_split_struct.v"
    test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"

    flags = ["--cc", f"--trace-{fmt}", "--trace-structs", "--no-trace-params"]

    test.compile(verilator_flags2=flags)

    # When struct fields are driven from different clocks, the dtype
    # optimization cannot be applied -- no trace_chg_dtype functions should exist
    trace_cpp = test.obj_dir + "/" + test.vm_prefix + "__Trace__0.cpp"
    test.file_grep_count(trace_cpp, r"^ *Vt_.*trace_chg_dtype", 0)

    test.execute()

    test.trace_identical(test.trace_filename, test.golden_filename)

    test.passes()
