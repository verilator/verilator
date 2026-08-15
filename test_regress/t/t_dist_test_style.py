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


def get_source_files():
    git_files = test.run_capture("cd " + test.root + " && git ls-files")
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
        m = re.match(r'^(.*?)(' + pattern + ')(.*)', buf, re.DOTALL)
        if not m:
            break
        lineno += m.group(1).count("\n")
        ln = m.group(2)
        buf = m.group(3)
        test.error_keep_going(filename + ":" + str(lineno) + ": " + message + ": " + ln)


#####

if not os.path.exists(test.root + "/.git"):
    test.skip("Not in a git repository")

### Must trim output before and after our file list
files = get_source_files()

for filename in sorted(files.keys()):
    filename = os.path.join(test.root, filename)
    if not os.path.exists(filename):  # git file might be deleted but not yet staged
        continue
    if not re.search(r'test_regress/t/.*\.v$', filename):
        continue

    contents = test.file_contents(filename)

    check_pattern(
        filename, contents, r'`check[a-z]+\([^\n]*?randomize\(',
        "check macros have side effects, suggest assign to randomize_result variable and check that"
    )

test.passes()
