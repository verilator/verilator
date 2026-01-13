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

if not os.path.exists(test.root + "/.git"):
    test.skip("Not in a git repository")

### Must trim output before and after our file list
files = test.run_capture("cd " + test.root + " && git ls-files --exclude-standard")
if test.verbose:
    print("ST " + files)

names = {}
files = re.sub(r'\s+', ' ', files)

regex = r'(FIX[M]E|BO[Z]O)'
for filename in files.split():
    if "test_regress/t/t_0_uvm_dpi/" in filename:  # Standard file - can't change it
        continue
    if re.search(regex, filename):
        names[filename] = True
    filename = os.path.join(test.root, filename)
    if not os.path.exists(filename):
        continue
    wholefile = test.file_contents(filename)
    if re.search(regex, wholefile):
        names[filename] = True

if len(names):
    test.error("Files with FIX" + "MEs: " + ' '.join(sorted(names.keys())))

test.passes()
