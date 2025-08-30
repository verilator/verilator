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

FileTimes = {}


def prep_output_file(filename):
    oldstats = os.path.getmtime(filename)
    if not oldstats:
        test.error("No output file found: " + filename)
    print("Old %s mtime=%d" % (filename, oldstats))
    FileTimes[filename] = oldstats


def check_times():
    for filename, oldtime in FileTimes.items():
        newstats = os.path.getmtime(filename)
        print("New %s mtime=%d" % (filename, newstats))
        if oldtime != newstats:
            test.error("--skip-identical was ignored -- regenerated %s" % (filename))


test.scenarios('vlt')

test.setenv('VERILATOR_DEBUG_SKIP_HASH', "1")
test.compile(verilator_flags2=['--stats'])

print("NOTE: use --debugi, as --debug in driver turns off skip-identical")

prep_output_file(test.obj_dir + "/V" + test.name + ".cpp")
prep_output_file(test.obj_dir + "/V" + test.name + "__stats.txt")

time.sleep(2)  # Or else it might take < 1 second to compile and see no diff.

print("\nTest skip without hash fallback")
test.setenv('VERILATOR_DEBUG_SKIP_IDENTICAL', "1")
test.setenv('VERILATOR_DEBUG_SKIP_HASH', "1")
test.compile(verilator_flags2=['--stats'])
check_times()

time.sleep(2)  # Or else it might take < 1 second to compile and see no diff.

print("\nTest skip with hash fallback")
os.utime(test.top_filename, None)
test.setenv('VERILATOR_DEBUG_SKIP_IDENTICAL', "1")
test.setenv('VERILATOR_DEBUG_SKIP_HASH', "")
test.compile(verilator_flags2=['--stats'])
check_times()

test.passes()
