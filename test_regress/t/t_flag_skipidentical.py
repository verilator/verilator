#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import time

test.scenarios('vlt')

test.compile()

print("NOTE: use --debugi, as --debug in driver turns off skip-identical")

outfile = test.obj_dir + "/V" + test.name + ".cpp"
oldstats = os.path.getmtime(outfile)
if not oldstats:
    test.error("No output file found: " + outfile)
print("Old mtime=", oldstats)

time.sleep(2)  # Or else it might take < 1 second to compile and see no diff.

test.setenv('VERILATOR_DEBUG_SKIP_IDENTICAL', "1")
test.compile()

newstats = os.path.getmtime(outfile)
print("New mtime=", newstats)

if oldstats != newstats:
    test.error("--skip-identical was ignored -- recompiled")

test.passes()
