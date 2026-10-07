#!/usr/bin/env python3
# DESCRIPTION: Verilator: Check formatter version consistency
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

if not os.path.exists(test.root + "/.git"):
    test.skip("Not in a git repository")

requirements = set(
    re.findall(r'^([\w.-]+)==', test.file_contents(test.root + "/python-dev-requirements.txt"),
               re.MULTILINE))
config_filename = test.root + "/.pre-commit-config.yaml"
config = test.file_contents(config_filename)

clang_format = re.search(r'^CLANGFORMAT\s*=\s*(clang-format-\d+)\s*$',
                         test.file_contents(test.root + "/Makefile.in"), re.MULTILINE).group(1)

for formatter in re.findall(r'^\s*entry:\s+(\S+)', config, re.MULTILINE):
    if formatter == 'chmod':
        continue
    if formatter.startswith('clang-format'):
        if formatter != clang_format:
            test.error_keep_going(config_filename + ": " + formatter +
                                  " does not match Makefile.in (" + clang_format + ")")
    elif formatter not in requirements:
        test.error_keep_going(config_filename + ": " + formatter +
                              " must have a version pin in python-dev-requirements.txt")

test.passes()
