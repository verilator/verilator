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

### Must trim output before and after our file list
cmd = "cd " + root + " && git ls-files --exclude-standard"
files = test.run_capture(cmd)
if test.verbose:
    print("ST " + files)
names = {}
for filename in files.split():
    if "include/vltstd/vpi_user.h" in filename:  # IEEE Standard file - can't change it
        continue
    if "include/gtkwave/" in filename:  # Standard file - can't change it
        continue
    filename = os.path.join(root, filename)
    if not os.path.exists(filename):
        continue
    with open(filename, 'r', encoding='latin-1') as fh:
        for line in fh:
            if "include" not in line:
                continue
            line = line.rstrip()
            hit = (re.search(r'\bassert\.h', line) or re.search(r'\bctype\.h', line)
                   or re.search(r'\berrno\.h', line) or re.search(r'\bfloat\.h', line)
                   or re.search(r'\blimits\.h', line) or re.search(r'\blocale\.h', line)
                   or re.search(r'\bmath\.h', line) or re.search(r'\bsetjmp\.h', line)
                   or re.search(r'\bsignal\.h', line) or re.search(r'\bstdarg\.h', line)
                   or re.search(r'\bstdbool\.h', line) or re.search(r'\bstddef\.h', line)
                   or re.search(r'\bstdio\.h', line) or re.search(r'\bstdlib\.h', line)
                   or re.search(r'\bstring\.h', line)
                   or (re.search(r'\btime\.h', line) and not re.search(r'sys/time.h', line)))
            #Not yet: r'\bstdint\.h'
            if not hit:
                continue
            names[filename + ": " + line] = True

if len(names):
    test.error("Files like stdint.h instead of cstdint:\n    " +
               "\n    ".join(sorted(names.keys())))

test.passes()
