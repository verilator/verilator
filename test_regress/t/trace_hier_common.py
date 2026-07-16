# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


def run(test, *, verilator_flags2=()):
    fmt, = test.parse_name(r"t_trace_hier_([a-z]+)")

    # All test use the same SV file
    test.top_filename = "t/t_trace_hier.v"
    # Any variations after the format name must yield the exact same trace
    test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"

    flags = [
        f"--trace-{fmt}", "-j", "4", "t/t_trace_hier_sub/t_trace_hier.vlt", "--top-module", "t",
        "--hierarchical", "-F", "t/t_trace_hier_sub/top.vc"
    ]
    flags.extend(verilator_flags2)

    # Run test
    test.compile(verilator_flags2=flags)

    test.execute()

    test.trace_identical(test.trace_filename, test.golden_filename)

    test.passes()
