# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


def run(test):
    (fmt,) = test.parse_name(r"t_trace_struct_alias_([a-z]+)")

    test.top_filename = "t/t_trace_struct_alias.v"
    test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"

    flags = ["--cc", f"--trace-{fmt}", "--trace-structs"]

    test.compile(verilator_flags2=flags)

    test.execute()

    if fmt == "vcd":
        codes = test.vcd_extract_codes(test.trace_filename)

        test.vcd_check_not_aliased(codes, "top.t.s1.a", "top.t.s2.a")

        test.vcd_check_aliased(codes, "top.t.s3.a", "top.t.alias_of_s3a")

        test.vcd_check_aliased(codes, "top.t.s4.a", "top.t.s5.a")
        test.vcd_check_aliased(codes, "top.t.s4.b", "top.t.s5.b")

        test.vcd_check_aliased(codes, "top.t.s6.a", "top.t.source_val")

    test.trace_identical(test.trace_filename, test.golden_filename)

    test.passes()
