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
        test.error_keep_going(filename + ":" + str(lineno) + ": " + message)


def check_sorted(filename, contents):
    re_option = re.compile(r'^\.\. option:: (.*)')
    re_other = re.compile(r'^[^ ]')
    # .. t_dist_docs_style ignore string
    #    Ignore the given string, as a prefix match
    re_ignore = re.compile(r' *\.\. t_dist_docs_style ignore (.*)')
    # .. t_dist_docs_style restart_sort
    #    Restart the sort as if it's a new list, for forcing specific ordering
    re_restart = re.compile(r' *\.\. t_dist_docs_style restart_sort')

    contents += "__EOF__\n"

    lineno = 0
    options = []
    ignores = []
    for line in contents.split("\n"):
        lineno += 1
        if re.match(r'^($|\.\. _)', line):
            continue
        match_option = re_option.match(line)
        match_ignore = re_ignore.match(line)
        if match_option:
            arg = match_option.group(1)
            # print("-option %s" % line)
            hit = False
            for ignore in ignores:
                if arg[:len(ignore)] == ignore:
                    hit = True
            if not hit:
                options.append([lineno, arg])
        elif match_ignore:
            arg = match_ignore.group(1)
            ignores.append(arg)
        elif (options and re_other.match(line)) or re_restart.match(line):
            # print("-end-list %d %s" % (len(options), line))
            check_sorted_options(filename, options)
            ignores = []
            options = []


def check_sorted_options(filename, options):
    last_opt = None
    for opt_data in options:
        (lineno, opt) = opt_data
        if last_opt and _option_sort_key(last_opt) > _option_sort_key(opt):
            test.error_keep_going(filename + ":" + str(lineno) +
                                  ": Option '%s' should be in sorted order before '%s'" %
                                  (opt, last_opt))
        last_opt = opt


def _option_sort_key(opt):
    opt = re.sub(r'^<', ' <', opt)  # <file> before -option
    opt = re.sub(r'^\+', '-', opt)  # +options sort with -options
    opt = re.sub(r'^--', '-', opt)  # -- sorts with -
    opt = re.sub(r'^-no-', '-', opt)  # -no- sorts with non-no
    opt = opt.lower()
    return opt


#####

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
    check_sorted(filename, contents)

test.passes()
