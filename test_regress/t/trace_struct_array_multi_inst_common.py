# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re


def _check_empty_scopes_vcd(test, vcd_filename):
    with open(vcd_filename, "r", encoding="utf-8") as f:
        lines = f.readlines()

    scope_stack = []
    for line in lines:
        line = line.strip()
        if "$scope" in line:
            scope_stack.append({"name": line, "has_var": False})
        elif "$var" in line:
            for scope in scope_stack:
                scope["has_var"] = True
        elif "$upscope" in line:
            if scope_stack:
                scope = scope_stack.pop()
                if not scope["has_var"]:
                    test.error("Empty scope hierarchy: " + scope["name"] +
                               " (no variables in scope or any child scopes)")
        elif "$enddefinitions" in line:
            break


def _check_empty_scopes_saif(test, saif_filename):
    with open(saif_filename, "r", encoding="utf-8") as f:
        content = f.read()

    instance_stack = []
    for line in content.splitlines():
        stripped = line.strip()
        m = re.match(r"\(INSTANCE\s+(\S+)", stripped)
        if m:
            instance_stack.append({"name": m.group(1), "has_net": False})
        elif stripped.startswith("(NET"):
            for inst in instance_stack:
                inst["has_net"] = True
        elif stripped == ")" and instance_stack:
            inst = instance_stack.pop()
            if not inst["has_net"]:
                test.error("Empty INSTANCE in SAIF: " + inst["name"] +
                           " (no NET in instance or any child instances)")


def run(test):
    mode, fmt = test.parse_name(r"t_trace_struct_array_multi_inst_(cc|sc)_([a-z]+)")

    if mode == "sc" and not test.have_sc:
        test.skip("No SystemC installed")

    test.top_filename = "t/t_trace_struct_array_multi_inst.v"
    test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"

    flags = [
        f"--{mode}",
        f"--trace-{fmt}",
        "--trace-structs",
        "--output-split-ctrace",
        "10",
    ]

    test.compile(verilator_flags2=flags)

    test.execute()

    test.trace_identical(test.trace_filename, test.golden_filename)

    if fmt in ("fst", "vcd"):
        _check_empty_scopes_vcd(test, test.golden_filename)
    elif fmt == "saif":
        _check_empty_scopes_saif(test, test.trace_filename)

    test.passes()
