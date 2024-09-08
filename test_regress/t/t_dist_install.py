#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

root = ".."

if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

cwd = os.getcwd()
destdir = cwd + "/" + test.obj_dir

# Start clean
test.run(cmd=["rm -rf " + destdir + " && mkdir -p " + destdir], check_finished=False)

# Install into temp area
print("Install...")
test.run(cmd=["cd " + root + " && " + os.environ["MAKE"] + " DESTDIR=" + destdir + " install-all"],
         check_finished=False)

# Check we can run a test
# Unfortunately the prefix was hardcoded in the exec at a different place,
# so we can't do much here.
#print("Check install...")

# Uninstall
print("Uninstall...\n")
test.run(cmd=["cd " + root + " && " + os.environ["MAKE"] + " DESTDIR=" + destdir + " uninstall"],
         check_finished=False)

# Check empty
files = []
finds = test.run_capture("find " + destdir + " -type f -print")
for filename in finds.split():
    if re.search(r'\.status', filename):  # Made by driver.py, not Verilator
        continue
    print("\tLEFT:  " + filename)
    filename = re.sub(r'^' + re.escape(cwd), '.', filename)
    files.append(filename)

if len(files) > 0:
    test.error("Uninstall missed files: " + ' '.join(files))

test.passes()
