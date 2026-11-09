# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


def run(test):
    fmt, = test.parse_name(r"t_trace_dumpvars_sparse_([a-z]+)")

    test.top_filename = "t/t_trace_dumpvars_sparse.v"

    test.compile(
        make_main=False,
        verilator_flags2=[
            "--cc",
            "--exe",
            f"--trace-{fmt}",
            "t/t_trace_dumpvars_sparse.cpp",
            "-CFLAGS",
            f"-DTRACE_FMT={fmt}",
            "-CFLAGS",
            f"-DTRACE_HEADER_C=verilated_{fmt}_c.h",
            "-CFLAGS",
            f"-DVERILATED_TRACE_C=Verilated{fmt.capitalize()}C",
            # Bounds-check std::vector<bool> indexing in the trace runtime
            "-CFLAGS",
            "-D_GLIBCXX_DEBUG",
        ])

    test.execute()

    test.trace_identical(test.trace_filename, test.golden_filename)

    test.passes()
