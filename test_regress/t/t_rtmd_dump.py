#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')


def compile_model(prefix, extra_flags):
    test.vm_prefix = prefix
    # Each model needs its own main, as they share the object directory
    test.main_filename = test.obj_dir + "/" + test.vm_prefix + "__main.cpp"
    test.run(cmd=["cp", test.pli_filename, test.main_filename])
    test.compile(make_main=False,
                 verilator_flags2=["--cc", "--rtmd", "--timing", "--exe", test.main_filename] +
                 extra_flags)


# Compile hierarchically
compile_model("Vhier", ["--hierarchical"])
# Compile non-hierarchically
compile_model("Vnonh", [])

# Both builds must print the same hierarchy, but vary based on:
# - with a named root, and with an unnamed root
# - with and without splitting signals into their components
for topname in ("TOP", ""):
    for split in (True, False):
        suffix = ("" if topname else "_notop") + ("_split" if split else "")
        golden = test.golden_filename.replace(".out", suffix + ".out")
        flags = ["+topname=" + topname] + (["+split"] if split else [])
        for prefix in ("Vhier", "Vnonh"):
            test.execute(executable=test.obj_dir + "/" + prefix,
                         all_run_flags=flags,
                         expect_filename=golden)

test.passes()
