#!/usr/bin/env python3
# DESCRIPTION: Verilator: Primitive C++ style checker
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

root = ".."


def get_source_files(root):
    git_files = test.run_capture("cd " + root + " && git ls-files")
    if test.verbose:
        print("MF " + git_files)
    files = {}
    for filename in git_files.split():
        if filename == '':
            continue
        files[filename] = True
    return files


def check_pattern(filename, contents, pattern, message):
    lineno = 1
    buf = contents
    while True:
        m = re.match(r'^(.*?^(' + pattern + '))(.*)', buf)
        if not m:
            break
        lineno += m.group(1).count("\n")
        buf = m.group(3)
        test.error(filename + ":" + str(lineno) + ": " + message)


if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

### Must trim output before and after our file list
files = get_source_files(root)

for filename in sorted(files.keys()):
    filename = os.path.join(root, filename)
    if not os.path.exists(filename):  # git file might be deleted but not yet staged
        continue
    if not re.search(r'\.rst$', filename):
        continue

    contents = test.file_contents(filename)

    check_pattern(filename, contents, r'.*[a-z](?<!:ref):\`[^`]+\n',
                  "tag:`...` should not be split between lines")
    check_pattern(filename, contents, r'.*[a-z](?<!:ref):\'',
                  "tag:`...' should use backticks instead")

test.passes()
