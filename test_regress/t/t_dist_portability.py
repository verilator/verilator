#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

root = ".."


def line_filename(line):
    m = re.search(r'^([^:]+)', line)
    return m.group(1) if m else 'UNKNOWN'


def printfll():
    files = "src/*.c* src/*.h include/*.c* include/*.h examples/*/*.c* test_regress/t/*.c* test_regress/t/*.h"
    cmd = "cd " + root + " && fgrep -n ll " + files + " | sort"
    grep = test.run_capture(cmd, check=False)
    names = {}
    for line in grep.splitlines():
        if not re.search(r'%[a-z0-9]*ll', line):
            continue
        if re.search(r'lintok-format-ll', line):
            continue
        print(line)
        names[line_filename(line)] = True
    if len(names):
        test.error("Files with %ll instead of PRIx64: " + ' '.join(sorted(names.keys())))


def cstr():
    files = "src/*.c* src/*.h include/*.c* include/*.h examples/*/*.c* test_regress/t/*.c* test_regress/t/*.h"
    cmd = "cd " + root + " && grep -n -P 'c_str|begin|end' " + files + " | sort"
    grep = test.run_capture(cmd, check=False)
    names = {}
    for line in grep.splitlines():
        if re.search(r'^([^:]+)[^"]*\(\)[a-z0-9_().->]*[.->]+(c_str|r?begin|r?end)\(\)', line):
            if re.search(r'lintok-begin-on-ref', line):
                continue
            print(line)
            names[line_filename(line)] = True
    if len(names):
        test.error("Files with potential c_str() lifetime issue: " +
                   ' '.join(sorted(names.keys())))


def vsnprintf():
    # Note do not do test_regress, as VPI files need to compile without verilatedos.h
    files = "src/*.c* src/*.h include/*.c* include/*.h examples/*/*.c*"
    cmd = "cd " + root + " && grep -n -P '(snprintf|vsnprintf)' " + files + " | sort"
    grep = test.run_capture(cmd, check=False)
    names = {}
    for line in grep.splitlines():
        if re.search(r'\b(snprintf|vsnprintf)\b', line):
            if re.search(r'# *define\s*VL_V?SNPRINTF', line):
                continue
            print(line)
            names[line_filename(line)] = True
    if len(names):
        test.error("Files with vsnprintf, use VL_VSNPRINTF: " + ' '.join(sorted(names.keys())))


def final():
    # Note do not do test_regress, as VPI files need to compile without verilatedos.h
    files = "src/*.c* src/*.h include/*.c* include/*.h"
    cmd = "cd " + root + " && grep -n -P '(class|struct)' " + files + " | sort"
    grep = test.run_capture(cmd, check=False)
    names = {}
    for line in grep.splitlines():
        if re.search(r':\s*(class|struct) ', line):
            if (re.search(r'final|VL_NOT_FINAL', line)  #
                    or re.search(r'{}', line)  # e.g. 'class Foo {};'
                    or re.search(r';', line)  # e.g. 'class Foo;'
                    or re.search(r'(class|struct)\s+{', line)  # e.g. anon 'class {'
                    or re.search(r'struct std::', line)  #
                    or not re.search(r'{', line)):
                continue
            print(line)
            names[line_filename(line)] = True
    if len(names):
        test.error("Files with classes without final/VL_NOT_FINAL: " +
                   ' '.join(sorted(names.keys())))


if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

printfll()
cstr()
vsnprintf()
final()

test.passes()
