#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

# Build 3 flavours: flat, --hierarchical, manual --lib-create, all should be the same


def lib_create(name, extra_flags):
    test.vm_prefix = "Vlib_" + name
    # Single threaded, as the library is evaluated within the threads of the model using it
    test.compile(make_main=False,
                 threads=1,
                 verilator_make_gmake=False,
                 verilator_flags2=extra_flags + ["--lib-create", name, "--top-module", name])
    test.run(logfile=test.obj_dir + "/" + test.vm_prefix + "_make.log",
             cmd=[
                 os.environ["MAKE"], "-C", test.obj_dir, "-f", test.vm_prefix + ".mk",
                 "lib" + name + ".a"
             ])


lib_create("leaf", [])
lib_create("sub", ["+define+USE_LIB_LEAF", test.obj_dir + "/leaf.sv", "libleaf.a"])


def compile_model(prefix, extra_flags):
    test.vm_prefix = prefix
    # Each model needs its own main, as they share the object directory
    test.main_filename = test.obj_dir + "/" + test.vm_prefix + "__main.cpp"
    test.compile(verilator_flags2=extra_flags)


compile_model("Vnonh", [])
compile_model("Vhier", ["--hierarchical"])
compile_model("Vlibs", [
    "+define+USE_LIB_LEAF", "+define+USE_LIB_SUB", test.obj_dir + "/sub.sv", "libsub.a",
    "libleaf.a"
])

# Hierarchical, non-hierarchical and library builds must all print the same %m
for prefix in ("Vnonh", "Vhier", "Vlibs"):
    test.execute(executable=test.obj_dir + "/" + prefix, expect_filename=test.golden_filename)

test.passes()
