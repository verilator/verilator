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

Waivers = [
    '+verilator+prof+threads+file+',  # Deprecated
    '+verilator+prof+threads+start+',  # Deprecated
    '+verilator+prof+threads+window+',  # Deprecated
    '-fno-',  # Documented differently
    '-no-lineno',  # Deprecated
    '-no-order-clock-delay',  # Deprecated
    '-prof-threads',  # Deprecated
]


def get_summary_opts(root):
    args = {}
    for filename in test.glob_some(root + "/bin/*"):
        with open(filename, "r", encoding="latin-1") as fh:
            on = False
            lineno = 0
            for line in fh:
                lineno += 1
                line = line.rstrip()
                m1 = re.search(r'^\s+((-|\+)+[^ ]+)', line)
                m2 = re.search(r"parser.add_argument\('((-|\+)[^']+)'", line)
                if re.search(r'ARGUMENT SUMMARY', line):
                    on = True
                elif re.search(r'=head1', line):
                    on = False
                elif on and m1:
                    opt = opt_clean(m1.group(1))
                    if test.verbose:
                        print("S '" + opt + "' " + line)
                    args[opt] = filename + ":" + str(lineno)
                elif m2:
                    opt = opt_clean(m2.group(1))
                    if test.verbose:
                        print("S '" + opt + "' " + line)
                    args[opt] = filename + ":" + str(lineno)
    return args


def get_docs_opts(root):
    args = {}
    for filename in test.glob_some(root + "/docs/guide/*.rst"):
        with open(filename, "r", encoding="latin-1") as fh:
            lineno = 0
            for line in fh:
                lineno += 1
                line = line.rstrip()
                m = re.search(r'option:: ((-|\+)+[^ `]+)', line)
                if not m:
                    m = re.search(r':vlopt:`[^`]+ <([^>]+)>', line)
                if not m:
                    m = re.search(r':vlopt:`((-|\+)+[^ `]+)', line)
                if m:
                    opt = opt_clean(m.group(1))
                    if test.verbose:
                        print("D '" + opt + "' " + line)
                    args[opt] = filename + ":" + str(lineno)
    return args


def opt_clean(opt):
    opt = re.sub(r'--', '-', opt)
    opt = re.sub(r'<.*', '', opt)
    opt = re.sub(r'\\', '', opt)
    return opt


def alt_names(opt):
    opts = [opt]
    if re.search(r'^-', opt):
        opts.append("-no" + opt)
    m = re.search(r'^-no(-.*)', opt)
    if m:
        opts.append(m.group(1))
    return opts


if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

sums = get_summary_opts(root)
docs = get_docs_opts(root)

both = {}
both.update(sums)
both.update(docs)

waiver = {k: 1 for k in Waivers}

for opt in sorted(both.keys()):
    if opt in waiver:
        continue
    sum_ok = False
    docs_ok = False
    for alt in alt_names(opt):
        if alt in sums:
            sum_ok = True
        if test.verbose:
            print(str(sum_ok) + " SAC '" + opt + "' -> '" + alt + "'")
    if re.search(r'-fno-', opt):  # Minimal-documented optimization option
        sum_ok = True
    for alt in alt_names(opt):
        if alt in docs:
            docs_ok = True
        if test.verbose:
            print(str(docs_ok) + " DAC '" + opt + "' -> '" + alt + "'")

    if not sum_ok:
        test.error(docs[opt] + ": Option documented in docs/guide '" + opt +
                   "' not found in bin/* ARGUMENT SUMMARY documentation")
    elif not docs_ok:
        test.error(sums[opt] + ": Option documented in bin/ ARGUMENT SUMMARY '" + opt +
                   "' not found in docs/guide documentation")
    elif test.verbose:
        print(": ok '" + opt)

test.passes()
