# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os


def run(test, *, verilator_flags2=()):
    variant, fmt = test.parse_name(r"t_trace_cat_(opennext|reopen|renew)_([a-z]+)")

    # All test use the same SV file
    test.top_filename = "t/t_trace_cat.v"
    # Any variations after the format name must yield the exact same trace
    test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"

    flags = [
        "--exe",
        f"--trace-{fmt}",
        "t/t_trace_cat.cpp",
        "-CFLAGS",
        f"-DTRACE_FMT={fmt}",
        "-CFLAGS",
        f"-DTRACE_HEADER_C=verilated_{fmt}_c.h",
        "-CFLAGS",
        f"-DVERILATED_TRACE_C=Verilated{fmt.capitalize()}C",
    ]
    match variant:
        case "opennext":
            flags.extend(["-CFLAGS", "-DTRACE_OPENNEXT"])
        case "reopen":
            flags.extend(["-CFLAGS", "-DTRACE_REOPEN"])
        case "renew":
            flags.extend(["-CFLAGS", "-DTRACE_RENEW"])
    flags.extend(verilator_flags2)

    # Run test
    test.compile(make_top_shell=False, make_main=False, verilator_flags2=flags)

    test.execute()

    if variant == "opennext":
        os.system("cat" +  \
                  " " + test.obj_dir + "/simx_part_0000.vcd" + \
                  " " + test.obj_dir + "/simx_part_0000_cat*.vcd" + \
                  " > " + test.obj_dir + "/simall.vcd")
        test.vcd_identical(test.obj_dir + "/simall.vcd", test.golden_filename)
    else:
        test.trace_identical(test.trace_filename.replace(f".{fmt}", f"_part_0000.{fmt}"),
                             test.golden_filename.replace(".out", "_part_0000.out"))
        test.trace_identical(test.trace_filename.replace(f".{fmt}", f"_part_0100.{fmt}"),
                             test.golden_filename.replace(".out", "_part_0100.out"))

    test.passes()
