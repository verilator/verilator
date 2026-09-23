#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.threads = 2 if test.vltmt else 1

for mode, flags, global_public in [
    ("global", ["--public-flat-rw"], 1),
    ("selective", [], 0),
]:
    ref_dir = test.obj_dir + "/" + mode + "_ref"
    opt_dir = test.obj_dir + "/" + mode + "_opt"
    # The feedback case intentionally retains a process-level cycle.
    common = ["--stats", "--build", "-Wno-UNOPTFLAT", *flags]
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
        '-CFLAGS "-I ../' + mode + '_ref -DTEST_GLOBAL=' + str(global_public) + '"',
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
