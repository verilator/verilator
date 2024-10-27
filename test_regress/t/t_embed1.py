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

child_dir = test.obj_dir + "_child"
test.mkdir_ok(child_dir)

# Compile the child
while True:
    cmdargs = test.compile_vlt_cmd(
        vm_prefix=test.vm_prefix + "_child",
        top_filename=test.name + "_child.v",
        verilator_flags=["-cc", "-Mdir", child_dir, "--debug-check"],
        # Can't use multi threading (like hier blocks), but needs to be thread safe
        threads=1)  # yapf:disable

    test.run(logfile=child_dir + "/vlt_compile.log", cmd=cmdargs)

    test.run(
        logfile=child_dir + "/vlt_gcc.log",
        cmd=[os.environ["MAKE"], "-C", child_dir,
            "-f" + os.getcwd() + "/Makefile_obj",
            "CPPFLAGS_DRIVER=-D"+test.name.upper(),
            ("CPPFLAGS_DRIVER2=-DTEST_VERBOSE=1" if test.verbose else ""),
            "VM_PREFIX=" + test.vm_prefix + "_child",
            "V" + test.name + "_child__ALL.a"  # bypass default rule, make archive
        ])  # yapf:disable

    break

# Compile the parent (might be with other than verilator)
test.compile(v_flags2=[os.path.abspath(child_dir + "/V" + test.name + "_child__ALL.a"),
                       # TODO would be nice to have this in embedded archive
                       "t/t_embed1_c.cpp"])  # yapf:disable

test.execute()

test.passes()
