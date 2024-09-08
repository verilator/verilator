#!/usr/bin/env python3
# DESCRIPTION: Verilator: Hacky import order checker, used to ensure all getters
# come before setters for consistent codegen when using autocxx (#5182)
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


if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

### Must trim output before and after our file list
files = get_source_files(root)

for filename in sorted(files.keys()):
    filename = os.path.join(root, filename)
    if not os.path.exists(filename):  # git file might be deleted but not yet staged
        continue
    if not re.search(r'include.*verilated.*\.[ch].*$', filename):
        continue
    if re.search(r'gtkwave', filename):
        continue

    contents = test.file_contents(filename) + "\n\n"
    seen_setters = {}
    seen_getters = {}
    lineno = 0
    for line in contents.splitlines():
        lineno += 1
        if re.search(r'^\s*\/\/', line):  # skip commented lines
            continue
        #print("L "+line)
        if re.search(r'^class', line):
            seen_setters = {}
            seen_getters = {}
            if test.verbose:
                print("C " + line)
            continue
        m = re.search(r'\s*void\s+([a-zA-Z0-9_]+)\([a-zA-Z0-9_]+.*', line)
        if m:
            setter_name = m.group(1)
            if test.verbose:
                print("S " + setter_name + " " + line)
            seen_setters[setter_name] = True
        m = re.search(r'\s*[a-zA-Z0-9_]+\s+([a-zA-Z0-9_]+)\(\s*\)', line)
        if m:
            getter_name = m.group(1)
            if getter_name == "cycle" and re.search(r'verilated_sc_trace', filename):
                continue  # hardcoded check for cycle() which looks like a setter but isn't
            if test.verbose:
                print("G " + setter_name + " " + line)
            if getter_name in seen_setters and getter_name not in seen_getters:
                test.error(filename + ":" + str(lineno) + ": '" + getter_name +
                           "()' came after its setter; swap order")
                seen_getters[getter_name] = True

test.passes()
