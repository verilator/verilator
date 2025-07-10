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

# Read expected source lines hit
expectedLines = set()

with open(root + "/src/V3DfgBreakCycles.cpp", 'r', encoding="utf8") as fd:
    for lineno, line in enumerate(fd, 1):
        line = line.split("//")[0]
        if re.match(r'^[^#]*SET_RESULT', line):
            expectedLines.add(lineno)

if not expectedLines:
    test.error("Failed to read expected source line numbers")

# Generate the equivalence checks and declaration boilerplate
rdFile = test.top_filename
plistFile = test.obj_dir + "/portlist.vh"
pdeclFile = test.obj_dir + "/portdecl.vh"
checkFile = test.obj_dir + "/checks.h"
nExpectedCycles = 0
with open(rdFile, 'r', encoding="utf8") as rdFh, \
     open(plistFile, 'w', encoding="utf8") as plistFh, \
     open(pdeclFile, 'w', encoding="utf8") as pdeclFh, \
     open(checkFile, 'w', encoding="utf8") as checkFh:
    for line in rdFh:
        line = line.split("//")[0]
        m = re.search(r'`signal\((\w+),', line)
        if not m:
            continue
        nExpectedCycles += 1
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
    "-fno-dfg-break-cycles",
    "+incdir+" + test.obj_dir,
    "-Mdir", test.obj_dir + "/obj_ref",
    "--prefix", "Vref",
    "-Wno-UNOPTFLAT"
])  # yapf:disable

# Check we got the expected number of circular logic warnings
test.file_grep(test.obj_dir + "/obj_ref/Vref__stats.txt",
               r'Warnings, Suppressed UNOPTFLAT\s+(\d+)', nExpectedCycles)

# Compile optimized - also builds executable
test.compile(verilator_flags2=[
    "--stats",
    "--build",
    "--exe",
    "+incdir+" + test.obj_dir,
    "-Mdir", test.obj_dir + "/obj_opt",
    "--prefix", "Vopt",
    "-Werror-UNOPTFLAT",
    "--dumpi-V3DfgBreakCycles", "9",  # To fill code coverage
    "-CFLAGS \"-I .. -I ../obj_ref\"",
    "../obj_ref/Vref__ALL.a",
    "../../t/" + test.name + ".cpp"
])  # yapf:disable

# Check all source lines hit
coveredLines = set()
with open(test.obj_dir + "/obj_opt/Vopt__V3DfgBreakCycles-TraceDriver-line-coverage.txt",
          'r',
          encoding="utf8") as fd:
    for line in fd:
        coveredLines.add(int(line.strip()))

if coveredLines != expectedLines:
    for n in sorted(expectedLines - coveredLines):
        test.error_keep_going(f"V3DfgBreakCycles.cpp line {n} not covered")
    for n in sorted(coveredLines - expectedLines):
        test.error_keep_going(f"V3DfgBreakCycles.cpp line {n} covered but not expected")

# Execute test to check equivalence
test.execute(executable=test.obj_dir + "/obj_opt/Vopt")

test.passes()
