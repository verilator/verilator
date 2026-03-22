# pylint: disable=R0914
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import re


def run(test, *, verilator_flags2=()):
    variant, fmt = test.parse_name(r"t_trace_lib_(default|notop)_([a-z]+)")

    # All test use the same SV file
    test.top_filename = "t/t_trace_lib.v"
    # Any variations after the format name must yield the exact same trace
    test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"

    verilator_common_flags = [
        "--cc",
        "--trace-threads",
        "1",
        f"--trace-{fmt}",
        "--trace-underscore",  # Should not trace __Vhandle
        "--trace-max-width",
        "0",
        "--trace-max-array",
        "0",
        "--trace-structs"
    ]

    main_top_name = "top"
    match variant:
        case "default":
            pass
        case "notop":
            main_top_name = ""
        case _:
            test.error(f"Unhandled test variant '{variant}'")

    verilator_common_flags.extend(verilator_flags2)

    # Compile sub0 --lib-create
    test.vm_prefix = "Vsub0"
    test.compile(make_main=False,
                 threads=1,
                 verilator_make_gmake=False,
                 verilator_flags2=verilator_common_flags + [
                     "+define+SUB0",
                     "--lib-create",
                     "sub0",
                     "--top-module",
                     "sub0",
                 ])
    test.run(logfile=test.obj_dir + "/Vsub0_make.log",
             cmd=[os.environ["MAKE"], "-C", test.obj_dir, "-f", "Vsub0.mk", "libsub0.a"])
    # Compile sub1 --lib-create
    test.vm_prefix = "Vsub1"
    test.compile(make_main=False,
                 threads=1,
                 verilator_make_gmake=False,
                 verilator_flags2=verilator_common_flags + [
                     "+define+SUB1",
                     "--lib-create",
                     "sub1",
                     "--top-module",
                     "sub1",
                 ])
    test.run(logfile=test.obj_dir + "/Vsub1_make.log",
             cmd=[os.environ["MAKE"], "-C", test.obj_dir, "-f", "Vsub1.mk", "libsub1.a"])
    # Compile top with libraries
    test.vm_prefix = "Vlibs"
    test.compile(main_top_name=main_top_name,
                 verilator_flags2=verilator_common_flags + [
                     "+define+TOP", test.obj_dir + "/sub0.sv", "libsub0.a",
                     test.obj_dir + "/sub1.sv", "libsub1.a"
                 ])

    # Compile simply without libraries
    test.vm_prefix = "Vnonl"
    test.main_filename = test.obj_dir + "/Vnonl__main.cpp"
    test.compile(main_top_name=main_top_name,
                 verilator_flags2=verilator_common_flags +
                 ["+define+TOP", "+define+SUB0", "+define+SUB1"])

    trace_libs = test.trace_filename.replace("simx", "libs")
    trace_nonl = test.trace_filename.replace("simx", "nonl")

    # Run the --lib-create model
    test.execute(executable=test.obj_dir + "/Vlibs")
    test.run(cmd=["mv", test.trace_filename, trace_libs])
    # Run the simple model without libraries
    test.execute(executable=test.obj_dir + "/Vnonl")
    test.run(cmd=["mv", test.trace_filename, trace_nonl])

    # Scope structure must match exactly, check only in vcd
    if fmt == "vcd":
        with open(trace_nonl, 'r', encoding='utf8') as fnonl, \
             open(trace_libs, 'r', encoding='utf8') as flibs:
            for la, lb in zip(fnonl, flibs):
                la = re.sub(r'^(\s*\$var\s+\S+\s+\S+\s+)\S+(.*)$', r'\1CODE\2', la)
                lb = re.sub(r'^(\s*\$var\s+\S+\s+\S+\s+)\S+(.*)$', r'\1CODE\2', lb)
                if la != lb:
                    test.error_keep_going("VCD header mismatch: '{}' !~ '{}'".format(
                        la.strip(), lb.strip()))
                if "enddefinitions" in la:
                    break

    # The two models must match ignoring enum attributes which can differ
    test.trace_identical(trace_libs, trace_nonl, ignore_attr=True)
    # The --lib-create must match the reference
    test.trace_identical(trace_libs, test.golden_filename)

    test.passes()
