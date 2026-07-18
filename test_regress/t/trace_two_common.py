# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os


def run(test, *, verilator_flags2=()):
    variant, mode, fmt = test.parse_name(r"t_trace_two_(dump|port|hdr)_(cc|sc)_([a-z]+).*")

    if mode == "sc" and not test.have_sc:
        test.skip("No SystemC installed")

    # All test use the same SV file
    test.top_filename = "t/t_trace_two_a.v"
    # Main driver file depends on mode
    main_filename = f"t/t_trace_two_{mode}.cpp"
    # Any variations after the format name must yield the exact same trace
    test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"

    common_flags = [
        f"--{mode}",
        f"--trace-{fmt}",
        f"+define+TRACE_FMT={fmt}",
        "-CFLAGS",
        f"-DTRACE_FMT={fmt}",
    ]
    match mode:
        case "cc":
            common_flags.extend([
                "-CFLAGS",
                f"-DTRACE_HEADER_C=verilated_{fmt}_c.h",
                "-CFLAGS",
                f"-DVERILATED_TRACE_C=Verilated{fmt.capitalize()}C",
            ])
        case "sc":
            common_flags.extend([
                "-CFLAGS",
                f"-DTRACE_HEADER_SC=verilated_{fmt}_sc.h",
                "-CFLAGS",
                f"-DVERILATED_TRACE_SC=Verilated{fmt.capitalize()}Sc",
            ])
        case _:
            test.error(f"Unhandled test mode '{mode}'")
    match variant:
        case "dump":
            common_flags.append("+define+TEST_DUMP")
        case "port":
            common_flags.append("+define+TEST_DUMPPORTS")
        case "hdr":
            common_flags.extend(["-CFLAGS", "-DTEST_HDR_TRACE=1"])
        case _:
            test.error(f"Unhandled test variant '{variant}'")
    common_flags.extend(verilator_flags2)

    # Verilate 'b'
    test.compile(make_main=False,
                 verilator_make_gmake=False,
                 top_filename='t_trace_two_b.v',
                 vm_prefix='Vt_trace_two_b',
                 verilator_flags2=common_flags)

    # Create the ALL.cpp for 'b'
    test.run(logfile=test.obj_dir + "/make_first_ALL.log",
             cmd=[
                 os.environ["MAKE"], "-C", "" + test.obj_dir, "-f", "Vt_trace_two_b.mk",
                 "Vt_trace_two_b__ALL.cpp"
             ])

    # Build 'a', this includes ALL.cpp for 'b'
    test.compile(make_main=False,
                 top_filename='t_trace_two_a.v',
                 verilator_flags2=common_flags + ['--exe', main_filename])

    test.execute()

    test.trace_identical(test.trace_filename, test.golden_filename)

    test.passes()
