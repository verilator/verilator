#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import collections

test.scenarios('vlt')


def preproc_check(filename1, filename2):
    # Read line comments.
    line_checks = collections.deque()
    with open(filename1, 'r', encoding="latin-1", newline='\n') as fh:
        lineno = 0
        for line in fh:
            lineno += 1
            if re.match(r'^Line_Preproc_Check', line):
                line_checks.append(lineno)

    # See if output file agrees.
    with open(filename2, 'r', encoding="latin-1", newline='\n') as fh:
        lineno = 0
        for line in fh:
            lineno += 1
            m = re.match(r'^\`line\s+(\d+)', line)
            if m:
                lineno = int(m.group(1)) - 1
            m = re.match(r'^Line_Preproc_Check\s+(\d+)', line)
            if m:
                linecmt = m.group(1)
                check = line_checks.popleft()
                file2ln = filename2 + ":" + str(lineno)
                if not check:
                    test.error(file2ln + ": Extra Line_Preproc_Check")
                if str(linecmt) != str(check):
                    test.error(file2ln + ": __LINE__ inserted " + str(linecmt) + ", exp=" +
                               str(check))
                if str(lineno) != str(check):
                    test.error(file2ln + ": __LINE__ on `line " + str(lineno) + ", exp=" +
                               str(check))

    if len(line_checks):
        test.error(filename2 + ": Missing a Line_Preproc_Check")


stdout_filename = test.obj_dir + "/" + test.name + "__test.vpp"

test.compile(verilator_flags2=['-DDEF_A0 -DPREDEF_COMMAND_LINE -E'],
             verilator_make_gmake=False,
             make_top_shell=False,
             make_main=False,
             stdout_filename=stdout_filename)

preproc_check(test.top_filename, stdout_filename)
test.files_identical(stdout_filename, test.golden_filename)

test.passes()
