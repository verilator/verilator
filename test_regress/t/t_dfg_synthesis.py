#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.sim_time = 2000000

root = ".."

if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

# Generate the equivalence checks and declaration boilerplate
rdFile = test.top_filename
plistFile = test.obj_dir + "/portlist.vh"
pdeclFile = test.obj_dir + "/portdecl.vh"
checkFile = test.obj_dir + "/checks.h"
nAlwaysSynthesized = 0
nAlwaysNotSynthesized = 0
nAlwaysReverted = 0
with open(rdFile, 'r', encoding="utf8") as rdFh, \
     open(plistFile, 'w', encoding="utf8") as plistFh, \
     open(pdeclFile, 'w', encoding="utf8") as pdeclFh, \
     open(checkFile, 'w', encoding="utf8") as checkFh:
    for line in rdFh:
        if re.search(r'^\s*always.*//\s*nosynth$', line):
            nAlwaysNotSynthesized += 1
        elif re.search(r'^\s*always.*//\s*revert$', line):
            nAlwaysReverted += 1
        elif re.search(r'^\s*always', line):
            nAlwaysSynthesized += 1
        line = line.split("//")[0]
        m = re.search(r'`signal\((\w+),', line)
        if not m:
            continue
        sig = m.group(1)
        plistFh.write(sig + ",\n")
        pdeclFh.write("output " + sig + ";\n")
        checkFh.write("if (ref." + sig + " != opt." + sig + ") {\n")
        checkFh.write("    std::cout << \"Mismatched " + sig + "\" << std::endl;\n")
        checkFh.write("    std::cout << \"Ref: 0x\" << std::hex << (ref." + sig +
                      " + 0) << std::endl;\n")
        checkFh.write("    std::cout << \"Opt: 0x\" << std::hex << (opt." + sig +
                      " + 0) << std::endl;\n")
        checkFh.write("    std::exit(1);\n")
        checkFh.write("}\n")

# Compile un-optimized
test.compile(verilator_flags2=[
    "--stats",
    "--build",
    "-fno-dfg",
    "+incdir+" + test.obj_dir,
    "-Mdir", test.obj_dir + "/obj_ref",
    "--prefix", "Vref",
    "-Wno-UNOPTFLAT"
])  # yapf:disable

test.file_grep_not(test.obj_dir + "/obj_ref/Vref__stats.txt", r'DFG.*Synthesis')

# Compile optimized - also builds executable
test.compile(verilator_flags2=[
    "--stats",
    "--build",
    "--fdfg-synthesize-all",
    "-fno-dfg-pre-inline",
    "-fno-dfg-post-inline",
    "--exe",
    "+incdir+" + test.obj_dir,
    "-Mdir", test.obj_dir + "/obj_opt",
    "--prefix", "Vopt",
    "-fno-const-before-dfg",  # Otherwise V3Const makes testing painful
    "-fno-split", # Dfg will take care of it
    "--debug", "--debugi", "0", "--dumpi-tree", "0",
    "-CFLAGS \"-I .. -I ../obj_ref\"",
    "../obj_ref/Vref__ALL.a",
    "../../t/" + test.name + ".cpp"
])  # yapf:disable

test.file_grep(test.obj_dir + "/obj_opt/Vopt__stats.txt",
               r'DFG scoped Synthesis, synt / always blocks considered\s+(\d+)$',
               nAlwaysSynthesized + nAlwaysReverted + nAlwaysNotSynthesized)
test.file_grep(test.obj_dir + "/obj_opt/Vopt__stats.txt",
               r'DFG scoped Synthesis, synt / always blocks synthesized\s+(\d+)$',
               nAlwaysSynthesized + nAlwaysReverted)
test.file_grep(test.obj_dir + "/obj_opt/Vopt__stats.txt",
               r'DFG scoped Synthesis, synt / reverted \(multidrive\)\s+(\d)$', nAlwaysReverted)

# Execute test to check equivalence
test.execute(executable=test.obj_dir + "/obj_opt/Vopt")

test.passes()
