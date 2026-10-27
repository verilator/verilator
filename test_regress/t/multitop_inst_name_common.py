# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os


def run(test, *, verilator_flags2=()):
    # All tests use the same SV file
    test.top_filename = "t/t_multitop_inst_name.v"
    flags = list(verilator_flags2)

    # Build 'sub' as a library, for the model using it
    test.vm_prefix = "Vlib_sub"
    # Single threaded, as the library is evaluated within the threads of the model using it
    test.compile(make_main=False,
                 threads=1,
                 verilator_make_gmake=False,
                 verilator_flags2=flags + ["--lib-create", "sub", "--top-module", "sub"])
    test.run(
        logfile=test.obj_dir + "/" + test.vm_prefix + "_make.log",
        cmd=[os.environ["MAKE"], "-C", test.obj_dir, "-f", test.vm_prefix + ".mk", "libsub.a"])

    # Build flat and with the library, both should be the same
    for prefix, extra_flags in (("Vnonh", []),
                                ("Vlibs",
                                 ["+define+USE_LIB", test.obj_dir + "/sub.sv", "libsub.a"])):
        test.vm_prefix = prefix
        test.compile(verilator_flags2=["--binary"] + flags + extra_flags)
        logfile = test.obj_dir + "/" + prefix + "__sim.log"
        test.execute(executable=test.obj_dir + "/" + prefix, logfile=logfile, check_finished=False)
        # Order of lines is unspecified, so don't use a golden file
        for name in ("top_a.u0", "top_a.u1", "top_bb.u0", "top_bb.u1"):
            test.file_grep(logfile, r"In '" + name + "'")

    test.passes()
