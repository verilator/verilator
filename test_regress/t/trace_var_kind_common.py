# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


def run(test):
    mode, fmt = test.parse_name(r"t_trace_var_kind_(cc|sc)_([a-z]+)")

    if mode == "sc" and not test.have_sc:
        test.skip("No SystemC installed")

    test.top_filename = "t/t_trace_var_kind.v"
    test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"

    flags = [f"--{mode}", f"--trace-{fmt}", "--trace-structs"]

    test.compile(verilator_flags2=flags)

    test.execute()

    test.trace_identical(test.trace_filename, test.golden_filename)

    test.passes()
