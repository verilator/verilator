#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(
    verilator_flags2=[
        "--prefix t_flag_prefix",  # should be overridden
        "--prefix Vprefix",
        "--exe",
        "--main",
        "--stats",
        "--build"
    ],
    verilator_make_cmake=False,
    verilator_make_gmake=False)

test.execute(executable=test.obj_dir + "/Vprefix")


def check_files():
    for path in test.glob_some(test.obj_dir + "/*"):
        filename = path[(len(test.obj_dir) + 1):]
        if re.search(r'\.log$', filename):
            continue
        if re.search(r't_flag_prefix', filename):
            test.error("bad filename '" + filename + "'")
            continue
        if re.search(r'^(.*\.(o|a)|Vprefix)$', filename):
            continue
        with open(path, 'r', encoding="utf8") as fh:
            for line in fh:
                line = re.sub(r'--prefix V?t_flag_prefix', '', line)
                line = re.sub(r'obj_vlt\/t_flag_prefix', '', line)
                line = re.sub(r't\/t_flag_prefix\.v', '', line)
                if re.search(r't_flag_prefix', line):
                    test.error(filename + ": bad line: " + line)


check_files()

test.passes()
