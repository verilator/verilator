# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


def run(test, *, verilator_flags2=()):
    variant, mode, fmt = test.parse_name(r"t_trace_complex_([a-z]+)_(cc|sc)_([a-z]+)")

    if mode == "sc" and not test.have_sc:
        test.skip("No SystemC installed")

    # All test use the same SV file
    test.top_filename = "t/t_trace_complex.v"
    # Any variations after the format name must yield the exact same trace
    test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"

    # Flags that influence expected results
    flags = [f"--{mode}", f"--trace-{fmt}"]
    match variant:
        case "default":
            pass
        case "params":
            flags.extend(["--trace-params", "--no-trace-structs"])
        case "structs":
            flags.extend(["--no-trace-params", "--trace-structs"])
        case _:
            test.error(f"Unhandled test variant '{variant}'")
    flags.extend(verilator_flags2)

    # Run test
    test.compile(verilator_flags2=flags)

    test.execute()

    test.trace_identical(test.trace_filename, test.golden_filename)

    test.passes()
