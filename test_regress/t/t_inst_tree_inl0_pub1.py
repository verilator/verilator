#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_inst_tree.v"

default_vltmt_threads = test.get_default_vltmt_threads
test.compile(
    verilator_flags2=['--stats', test.t_dir + "/" + test.name + ".vlt"],
    # Force 3 threads even if we have fewer cores
    threads=(default_vltmt_threads if test.vltmt else 1))


def check_relative_refs(mod, expect_relative):
    found_relative = False
    for filename in test.glob_some(test.obj_dir + "/V" + test.name + "_" + mod + "*.cpp"):
        if test.verbose:
            print("FILE " + filename)
        text = test.file_contents(filename)

        if re.search(r'this->', text) or re.search(r'vlSelf->', text):
            if test.verbose:
                print(" REL " + filename)
            found_relative = True

        if found_relative != expect_relative:
            test.error(filename + " " +
                       ("has 'relative'" if found_relative else "has 'non-relative'") +
                       " variable references but expected " +
                       ("'relative'" if expect_relative else "'non-relative'"))


if test.vlt_all:
    # We expect to combine sequent functions across multiple instances of
    # l2, l3, l4, l5. If this number drops, please confirm this has not broken.
    test.file_grep(test.stats, r'Optimizations, Combined CFuncs\s+(\d+)',
                   (85 if test.vltmt else 67))

    # Everything should use relative references
    check_relative_refs("t", True)
    check_relative_refs("l1", True)
    check_relative_refs("l2", True)
    check_relative_refs("l3", True)
    check_relative_refs("l4", True)
    check_relative_refs("l5__P1", True)
    check_relative_refs("l5__P2", True)

test.execute()
test.file_grep(test.run_log_filename, r"\] (%m|.*t\.ps): Clocked")

test.passes()
