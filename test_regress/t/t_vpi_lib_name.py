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

# Build 3 flavours: flat, --hierarchical, manual --lib-create, all should be the same
test.vm_prefix = "Vlib_sub"
# Single threaded, as the library is evaluated within the threads of the model using it
test.compile(make_main=False,
             threads=1,
             verilator_make_gmake=False,
             verilator_flags2=["--vpi", "--lib-create", "sub", "--top-module", "sub"])
test.run(logfile=test.obj_dir + "/" + test.vm_prefix + "_make.log",
         cmd=[os.environ["MAKE"], "-C", test.obj_dir, "-f", test.vm_prefix + ".mk", "libsub.a"])

for prefix, extra_flags in (("Vnonh", []), ("Vhier", ["--hierarchical"]),
                            ("Vlibs", ["+define+USE_LIB", test.obj_dir + "/sub.sv", "libsub.a"])):
    test.vm_prefix = prefix
    # Each model needs its own main, as they share the object directory
    main_filename = test.obj_dir + "/" + prefix + "__main.cpp"
    test.write_wholefile(main_filename,
                         "#include \"" + os.path.abspath(test.pli_filename) + "\"\n")
    test.compile(make_main=False,
                 make_top_shell=False,
                 verilator_flags2=["--exe", "--vpi", main_filename] + extra_flags)
    test.execute(executable=test.obj_dir + "/" + prefix,
                 logfile=test.obj_dir + "/" + prefix + "__sim.log")

test.passes()
