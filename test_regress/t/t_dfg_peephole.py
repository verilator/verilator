#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
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

# Read optimizations
optimizations = []

hdrFile = "../src/V3DfgPeephole.h"
with open(hdrFile, 'r', encoding="utf8") as hdrFh:
    prevOpt = ""
    lineno = 0
    for line in hdrFh:
        lineno += 1
        m = re.search(r'^\s*_FOR_EACH_DFG_PEEPHOLE_OPTIMIZATION_APPLY\(macro, (\w+)\)', line)
        if not m:
            continue
        opt = m.group(1)
        if prevOpt > opt:
            test.error(hdrFile + ":" + str(lineno) + ": '" + opt + "; is not in sorted order")
        prevOpt = opt
        optimizations.append(opt)

if len(optimizations) < 1:
    test.error("no optimizations defined in " + hdrFile)

# Generate the equivalence checks and declaration boilerplate
rdFile = test.top_filename
plistFile = test.obj_dir + "/portlist.vh"
pdeclFile = test.obj_dir + "/portdecl.vh"
checkFile = test.obj_dir + "/checks.h"
with open(rdFile, 'r', encoding="utf8") as rdFh, \
     open(plistFile, 'w', encoding="utf8") as plistFh, \
     open(pdeclFile, 'w', encoding="utf8") as pdeclFh, \
     open(checkFile, 'w', encoding="utf8") as checkFh:
    for line in rdFh:
        m = re.search(r'^\s*.*`signal\((\w+),', line)
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
    "--prefix", "Vref"
])  # yapf:disable

# Compile optimized - also builds executable
test.compile(verilator_flags2=[
    "--stats",
    "--build",
    "--exe",
    "+incdir+" + test.obj_dir,
    "-Mdir", test.obj_dir + "/obj_opt",
    "--prefix", "Vopt",
    "-fno-const-before-dfg",  # Otherwise V3Const makes testing painful
    "--dump-dfg",  # To fill code coverage
    "-CFLAGS \"-I .. -I ../obj_ref\"",
    "../obj_ref/Vref__ALL.a",
    "../../t/" + test.name + ".cpp"
])  # yapf:disable

# Execute test to check equivalence
test.execute(executable=test.obj_dir + "/obj_opt/Vopt")


def check(name):
    name = name.lower()
    name = re.sub(r'_', ' ', name)
    test.file_grep(test.obj_dir + "/obj_opt/Vopt__stats.txt",
                   r'DFG\s+(pre inline|post inline|scoped) Peephole, ' + name + r'\s+([1-9]\d*)')


# Check all optimizations defined in
for opt in optimizations:
    check(opt)

test.passes()
