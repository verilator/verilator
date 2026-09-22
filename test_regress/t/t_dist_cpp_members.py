#!/usr/bin/env python3
# DESCRIPTION: Verilator: Primitive C++ style checker
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')


def check():
    for filename in (test.glob_some(test.root + "/include/*.cpp") +
                     test.glob_some(test.root + "/include/*.h") +
                     test.glob_some(test.root + "/src/*.cpp") +
                     test.glob_some(test.root + "/src/*.h")):
        with open(filename, 'r', encoding="latin-1") as fh:
            lineno = 0
            in_class = False
            class_indent = ""
            last_was_comment = False
            for line in fh:
                line = line.rstrip()
                lineno += 1

                m = re.match(r'^(\s+)(class|struct) ', line)
                if m:
                    if test.verbose:
                        print(filename + ":" + str(lineno) + ": CLASS  : " + line)
                    in_class = True
                    class_indent = m.group(1)
                    continue
                if not in_class:
                    continue
                m = re.match(r'^(\s+)};', line)
                if m and m.group(1) == class_indent:
                    if test.verbose:
                        print(filename + ":" + str(lineno) + ": ENDCLS : " + line)
                    in_class = False
                    continue
                if re.match(r'^\s*// ', line) and not re.match(r'^\s*// MEMBER', line):
                    last_was_comment = True
                    continue

                if re.search(r' return ', line):
                    continue
                if re.search(r' VL_DO_', line):
                    continue
                # Member definitions (many false-negatives, but close enough for the rough purpose)
                if test.verbose:
                    print("? " + line)
                m = re.match(
                    r'^\s+(const\s+|static\s+)?[a-zA-Z0-9_]\S+\s+(const\s+)?(m_[a-zA-Z0-9_]+)(;|{| = )',
                    line)
                if m:
                    name = m.group(3)
                    if test.verbose:
                        print(filename + ":" + str(lineno) + ": MEMBER : " + line)
                    if not last_was_comment and not '//' in line and not '/*' in line:
                        test.error_keep_going(filename + ":" + str(lineno) + ": Member '" + name +
                                              "' is declared without any descriptive comment")

                last_was_comment = False


if not os.path.exists(test.root + "/.git"):
    test.skip("Not in a git repository")

check()

test.passes()
