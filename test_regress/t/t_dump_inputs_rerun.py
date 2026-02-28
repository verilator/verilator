#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')


def fixup(path):
    lines = []
    removeBeginKeywords = True
    with open(path, "r", encoding="utf-8") as rfd:
        for line in rfd:
            # Remove "all arguments" line, which can differ
            if line.startswith("//   Arguments:"):
                lines.append("//   Arguments: <REDACTED>")
            # Remove first `begin_keywords, which will be re-inserted on reruns
            elif removeBeginKeywords and line.startswith("`begin_keywords"):
                removeBeginKeywords = False
                lines.append("// " + line)
            else:
                lines.append(line)
    with open(path, "w", encoding="utf-8") as wfd:
        for line in lines:
            wfd.write(line)


obj_dir_1 = test.obj_dir + "/obj_dir_1"
test.mkdir_ok(obj_dir_1)
dump_1 = obj_dir_1 + "/Vprefix__inputs.vpp"
test.run(
    logfile=obj_dir_1 + "/vlt_compile.log",
    cmd=[
        "perl",
        os.environ["VERILATOR_ROOT"] + "/bin/verilator",
        "-cc",
        "-Mdir",
        obj_dir_1,
        "--prefix",
        "Vprefix",
        "--top-module",
        "lpm_divide",
        "--no-timing",
        "-CFLAGS",
        "'-O3 --foo'",  # Argument with whitespace
        "-CFLAGS",
        "'-DDQUOTE=\"'",  # Argument with quote
        "--dump-inputs",
        "t/t_altera_lpm.v",
        "t/t_math_cond_huge.v"
    ])
fixup(dump_1)

obj_dir_2 = test.obj_dir + "/obj_dir_2"
test.mkdir_ok(obj_dir_2)
dump_2 = obj_dir_2 + "/Vprefix__inputs.vpp"
test.run(
    logfile=obj_dir_2 + "/vlt_compile.log",
    cmd=[
        "perl",
        os.environ["VERILATOR_ROOT"] + "/bin/verilator",
        "-Mdir",
        obj_dir_2,
        "-f",
        dump_1,
        dump_1,
        "--debug",  # --debug also dumps the same way
        "--debugi",
        "1"
    ])
fixup(dump_2)

obj_dir_3 = test.obj_dir + "/obj_dir_3"
test.mkdir_ok(obj_dir_3)
dump_3 = obj_dir_3 + "/Vprefix__inputs.vpp"
test.run(logfile=obj_dir_3 + "/vlt_compile.log",
         cmd=[
             "perl",
             os.environ["VERILATOR_ROOT"] + "/bin/verilator",
             "-Mdir",
             obj_dir_3,
             "-f",
             dump_2,
             dump_2,
             "--dump-inputs",
         ])
fixup(dump_3)

test.files_identical(dump_1, dump_2)
test.files_identical(dump_1, dump_3)

test.passes()
