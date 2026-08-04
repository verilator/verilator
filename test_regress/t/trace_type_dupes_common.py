# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


def run(test):
    variant, fmt = test.parse_name(r"t_trace_type_dupes_([a-z]+)_([a-z]+)")

    test.top_filename = "t/t_trace_type_dupes.v"
    test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"

    flags = ["--cc", f"--trace-{fmt}"]
    match variant:
        case "default":
            pass
        case "structs":
            flags.extend(["--trace-structs", "--output-split-ctrace 10"])
        case _:
            test.error(f"Unhandled test variant '{variant}'")

    test.compile(verilator_flags2=flags)

    test.execute()

    test.trace_identical(test.trace_filename, test.golden_filename)

    test.passes()
