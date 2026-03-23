# pylint: disable=R0914
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re


def run(test, *, verilator_flags2=()):
    variant, mode, fmt = test.parse_name(
        r"t_trace_hier_block_(default|notop|statefulpkg)_(cc|sc)_([a-z]+)")

    # All test use the same SV file
    test.top_filename = "t/t_hier_block.v"
    # Any variations after the format name must yield the exact same trace
    test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"

    verilator_common_flags = []
    match mode:
        case "cc":
            verilator_common_flags.extend([  #
                "--cc",
            ])
        case "sc":
            verilator_common_flags.extend([  #
                "--sc",
                "--CFLAGS",
                '"-pipe -DCPP_MACRO=cplusplus"',
            ])
        case _:
            test.error(f"Unknown mode '{mode}'")

    verilator_common_flags.extend([
        f"--trace-{fmt}",
        "--trace-underscore",  # Should not trace __Vhandle
        "--trace-max-width",
        "0",
        "--trace-max-array",
        "0",
        "--trace-structs",
        "t/t_hier_block.cpp"
    ])

    main_top_name = "top"
    match variant:
        case "default":
            pass
        case "notop":
            main_top_name = ""
        case "statefulpkg":
            verilator_common_flags.append("+define+STATEFUL_PKG")
        case _:
            test.error(f"Unhandled test variant '{variant}'")

    verilator_common_flags.extend(verilator_flags2)
    verilator_hier_flags = verilator_common_flags + ['--hierarchical']

    # Compile hierarchically
    test.vm_prefix = "Vhier"
    test.main_filename = test.obj_dir + "/Vhier__main.cpp"
    test.compile(verilator_flags2=verilator_hier_flags, main_top_name=main_top_name)

    # Compile non-hierarchically
    test.vm_prefix = "Vnonh"
    test.main_filename = test.obj_dir + "/Vnonh__main.cpp"
    test.compile(verilator_flags2=verilator_common_flags, main_top_name=main_top_name)

    trace_hier = test.trace_filename.replace("simx", "hier")
    trace_nonh = test.trace_filename.replace("simx", "nonh")

    # Run the hierarchical model
    test.execute(executable=test.obj_dir + "/Vhier")
    test.run(cmd=["mv", test.trace_filename, trace_hier])
    # Run the non hierarchical model
    test.execute(executable=test.obj_dir + "/Vnonh")
    test.run(cmd=["mv", test.trace_filename, trace_nonh])

    if variant != "statefulpkg":
        # Scope structure must match exactly, check only in vcd
        if fmt == "vcd":
            with open(trace_nonh, 'r', encoding='utf8') as fnonh, \
                 open(trace_hier, 'r', encoding='utf8') as fhier:
                for la, lb in zip(fnonh, fhier):
                    la = re.sub(r'^(\s*\$var\s+\S+\s+\S+\s+)\S+(.*)$', r'\1CODE\2', la)
                    lb = re.sub(r'^(\s*\$var\s+\S+\s+\S+\s+)\S+(.*)$', r'\1CODE\2', lb)
                    if la != lb:
                        test.error_keep_going("VCD header mismatch: '{}' !~ '{}'".format(
                            la.strip(), lb.strip()))
                    if "enddefinitions" in la:
                        break

        # The two models must match ignoring enum attributes which can differ
        test.trace_identical(trace_hier, trace_nonh, ignore_attr=True)
    # The hierarchical must match the reference
    test.trace_identical(trace_hier, test.golden_filename)

    test.passes()
