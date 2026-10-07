#!/usr/bin/env python3
# DESCRIPTION: Verilator: Check formatter version consistency
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import shlex

test.scenarios('dist')

if not os.path.exists(test.root + "/.git"):
    test.skip("Not in a git repository")

requirements = dict(
    re.findall(r'^([\w.-]+)==(\S+)$',
               test.file_contents(test.root + "/python-dev-requirements.txt"), re.MULTILINE))
config_filename = test.root + "/.pre-commit-config.yaml"
config = test.file_contents(config_filename)

# System hooks share the development environment; any separate pins must agree.
for package, version in re.findall(r'\b([\w.-]+)==([\w.+-]+)', config):
    expected = requirements.get(package)
    if version != expected:
        test.error_keep_going(config_filename + ": " + package + "==" + version +
                              " does not match python-dev-requirements.txt (" + str(expected) +
                              ")")

clang_format = re.search(r'^CLANGFORMAT\s*=\s*(clang-format-\d+)\s*$',
                         test.file_contents(test.root + "/Makefile.in"), re.MULTILINE)
if not clang_format:
    test.error("Makefile.in: Missing versioned CLANGFORMAT command")

entries = re.findall(r'^\s*entry:\s*(?:&\w+\s+)?([^\n]+)', config, re.MULTILINE)
if not entries:
    test.error(config_filename + ": No formatter entries found")

for entry in entries:
    if entry.startswith('*'):
        continue  # The anchored entry is checked at its definition.
    command = shlex.split(entry)
    if command[0] == 'env':
        command.pop(0)
        while '=' in command[0]:
            command.pop(0)
    formatter = command[0]
    if formatter == 'chmod':
        continue
    if formatter.startswith('clang-format'):
        if formatter != clang_format.group(1):
            test.error_keep_going(config_filename + ": " + formatter +
                                  " does not match Makefile.in (" + clang_format.group(1) + ")")
    elif formatter not in requirements:
        test.error_keep_going(config_filename + ": " + formatter +
                              " must have a version pin in python-dev-requirements.txt")

test.passes()
