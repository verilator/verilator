#!/usr/bin/env python3
# DESCRIPTION: Verilator: Primitive C++ style checker
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

Waivers = [
    'Internal',
    'Unsupported',
    'DIDNOTCONVERGE',  # Runtime
]

src_filename = "src/V3Error.h"
doc_filename = "docs/guide/warnings.rst"


def get_src_warns():
    args = {}
    for filename in test.glob_some(test.root + "/" + src_filename):
        with open(filename, "r", encoding="latin-1") as fh:
            state = 0
            lineno = 0
            for line in fh:
                lineno += 1
                line = line.rstrip()
                line = re.sub(r'\s*//.*', '', line)
                # print("S: %s" % line)
                if state == 0 and re.search(r'class V3ErrorCode', line):
                    state = 1
                elif state == 1 and re.search(r'const names', line):
                    state = 2
                elif state == 2 and re.search(r' return ', line):
                    state = 3
                elif state == 2:
                    for opt in re.findall(r'"([A-Z0-9]+)"', line):
                        opt = opt_clean(opt)
                        if test.verbose:
                            print("S '" + opt + "' " + line)
                        args[opt] = filename + ":" + str(lineno)
    return args


def get_docs_warns():
    args = {}
    for filename in test.glob_some(test.root + "/" + doc_filename):
        with open(filename, "r", encoding="latin-1") as fh:
            lineno = 0
            last_opt = None
            for line in fh:
                lineno += 1
                line = line.rstrip()

                m = re.search(r' option:: ([A-Za-z0-9]+)', line)
                if m:
                    opt = opt_clean(m.group(1))
                    if test.verbose:
                        print("D '" + opt + "' " + line)
                    args[opt] = filename + ":" + str(lineno)
                    last_opt = opt

                if last_opt and re.search(r'Historical', line):
                    Waivers.append(last_opt)

    return args


def opt_clean(opt):
    return opt


if not os.path.exists(test.root + "/.git"):
    test.skip("Not in a git repository")

srcs = get_src_warns()
docs = get_docs_warns()
if len(srcs) < 10:
    test.error(src_filename + ": Too few warnings found; parse error?")
if len(docs) < 10:
    test.error(doc_filename + ": Too few warnings found; parse error?")

both = {}
both.update(srcs)
both.update(docs)

waiver = {k: 1 for k in Waivers}

for opt in sorted(both.keys()):
    if opt in waiver:
        continue
    src_ok = opt in srcs
    docs_ok = opt in docs

    if not src_ok:
        test.error_keep_going(docs[opt] + ": Warn code documented in " + doc_filename + " '" +
                              opt + "' not found in " + src_filename + " sources")
    elif not docs_ok:
        test.error_keep_going(srcs[opt] + ": Warn code documented in " + src_filename + " '" +
                              opt + "' not found in " + doc_filename + " documentation")
    elif test.verbose:
        print(": ok '" + opt)

test.passes()
