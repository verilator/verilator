#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

import re

test.scenarios('vlt_all')
test.threads = 2 if test.vltmt else 1

# Generate member access, paired writes and checks from the marked declarations.
declaration = re.compile(r'`(input_signal|output_signal|public_signal|public_array)\('
                         r'([A-Za-z_][A-Za-z_0-9]*),\s*(\d+)'
                         r'(?:,\s*(-?\d+),\s*(-?\d+))?\)\s*;')
signals = set()
members = set()
ports = []
num_checks = 0
with open(test.top_filename, 'r', encoding="utf8") as source, \
     open(test.obj_dir + "/signals.h", 'w', encoding="utf8") as access, \
     open(test.obj_dir + "/checks.h", 'w', encoding="utf8") as checks:
    for lineno, line in enumerate(source, 1):
        line = line.partition("//")[0].strip()
        if not re.match(r'`(?:input_signal|output_signal|public_signal|public_array)\b', line):
            continue
        match = declaration.fullmatch(line)
        if not match:
            test.error(f"Malformed signal declaration at {test.top_filename}:{lineno}")
        kind, name, width, lhs, rhs = match.groups()
        width = int(width)
        if not 1 <= width <= 64 or (kind == "public_array") != (lhs is not None):
            test.error(f"Unsupported signal declaration at {test.top_filename}:{lineno}")
        if name in signals:
            test.error("Duplicate signal declaration: " + name)
        signals.add(name)
        ctype = "CData" if width <= 8 else "SData" if width <= 16 else "IData" if width <= 32 else "QData"
        public = kind.startswith("public_")
        if not public:
            ports.append(name)
        member = ("rootp->t__DOT__" if public else "") + name
        indices = [None] if lhs is None else range(min(int(lhs), int(rhs)),
                                                   max(int(lhs), int(rhs)) + 1)
        for index in indices:
            suffix = "" if index is None else "_" + str(index).replace("-", "n")
            helper = name + suffix
            if helper in members:
                test.error("Duplicate generated accessor: " + helper)
            members.add(helper)
            field = member if index is None else member + f"[{index - min(int(lhs), int(rhs))}]"
            label = name if index is None else f"{name}[{index}]"
            access.write(f"{ctype} {helper}() const {{ return opt.{field}; }}\n")
            if kind == "input_signal" or public:
                access.write(
                    f"void {helper}({ctype} value) {{ ref.{field} = opt.{field} = value; }}\n")
            if kind == "output_signal" or public:
                access.write(f"void expect_{helper}({ctype} value) const {{ "
                             f'check("{label}", opt.{field}, value); }}\n')
                checks.write(f'check("{label}", opt.{field}, ref.{field});\n')
                num_checks += 1
if not num_checks:
    test.error("No signal checks generated from " + test.top_filename)
with open(test.obj_dir + "/portlist.vh", 'w', encoding="utf8") as portlist:
    portlist.write(",\n".join(ports) + "\n")

for mode, flags, global_public in [
    ("global", ["--public-flat-rw"], 1),
    ("selective", [], 0),
]:
    ref_dir = test.obj_dir + "/" + mode + "_ref"
    opt_dir = test.obj_dir + "/" + mode + "_opt"
    # The feedback case intentionally retains a process-level cycle.
    common = ["--stats", "--build", "-Wno-UNOPTFLAT", "+incdir+" + test.obj_dir, *flags]
    test.compile(verilator_flags2=[
        *common,
        "-fno-dfg",
        "-Mdir",
        ref_dir,
        "--prefix",
        "Vref",
    ])
    test.compile(verilator_flags2=[
        *common,
        "--exe",
        "-Mdir",
        opt_dir,
        "--prefix",
        "Vopt",
        "--debug",
        "--debugi",
        "0",
        "--dumpi-tree",
        "0",
        '-CFLAGS "-I .. -I ../' + mode + '_ref -DTEST_GLOBAL=' + str(global_public) + '"',
        "../" + mode + "_ref/Vref__ALL.a",
        "../../t/" + test.name + ".cpp",
    ])
    test.execute(executable=opt_dir + "/Vopt")
    test.file_grep_not(ref_dir + "/Vref__stats.txt", r'DFG.*Synthesis')
    test.file_grep(ref_dir + "/Vref__stats.txt", r'Warnings, Suppressed UNOPTFLAT\s+(\d+)$', 1)
    if global_public:
        test.file_grep(opt_dir + "/Vopt__stats.txt", r'Warnings, Suppressed UNOPTFLAT\s+(\d+)$', 1)
    else:
        test.file_grep_not(opt_dir + "/Vopt__stats.txt", r'Warnings, Suppressed UNOPTFLAT')
    test.file_grep(opt_dir + "/Vopt__stats.txt",
                   r'DFG, Synthesis, synt / always blocks considered\s+(\d+)$', 4)
    test.file_grep(opt_dir + "/Vopt__stats.txt",
                   r'DFG, Synthesis, synt / always blocks synthesized\s+(\d+)$', 0)
    test.file_grep(opt_dir + "/Vopt__stats.txt",
                   r'DFG, Synthesis, synt / non-synthesizable \(ext write\)\s+(\d+)$', 4)
    test.file_grep(opt_dir + "/Vopt__stats.txt",
                   r'DFG, Synthesis, synt / reverted \(non-synthesizable\)\s+(\d+)$', 4)

test.passes()
