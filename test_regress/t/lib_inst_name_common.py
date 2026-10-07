# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os


def run(test, *, verilator_flags2=(), lib_flags2=(), top_flags2=(), top="t"):
    # All tests use the same SV file
    test.top_filename = "t/t_lib_inst_name.v"
    flags = list(verilator_flags2)

    # Build 3 flavours: flat, --hierarchical, manual --lib-create, all should be the same
    test.vm_prefix = "Vlib_lib"
    # Single threaded, as the library is evaluated within the threads of the model using it
    test.compile(make_main=False,
                 threads=1,
                 verilator_make_gmake=False,
                 verilator_flags2=flags + list(lib_flags2) +
                 ["--lib-create", "lib", "--top-module", "lib"])
    test.run(
        logfile=test.obj_dir + "/" + test.vm_prefix + "_make.log",
        cmd=[os.environ["MAKE"], "-C", test.obj_dir, "-f", test.vm_prefix + ".mk", "liblib.a"])

    def compile_model(prefix, extra_flags):
        test.vm_prefix = prefix
        test.compile(verilator_flags2=["--binary"] + flags + list(top_flags2) + extra_flags)

    compile_model("Vnonh", [])
    compile_model("Vhier", ["--hierarchical"])
    compile_model("Vlibs", ["+define+USE_LIB", test.obj_dir + "/lib.sv", "liblib.a"])

    # The instances in the library are named as in the non-hierarchical build
    for prefix in ("Vnonh", "Vhier", "Vlibs"):
        logfile = test.obj_dir + "/" + prefix + "__sim.log"
        test.execute(executable=test.obj_dir + "/" + prefix, logfile=logfile, check_finished=False)
        # Order of lines is unspecified, so don't use a golden file
        for name in (top + ".u_lib.u0", top + ".u_lib.u1"):
            test.file_grep(logfile, r"In '" + name + "'")

    test.passes()
