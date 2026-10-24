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


def read_ast_nodes_cpp():
    for filename in (test.glob_some(test.root + "/src/V3AstNodes.cpp")):
        with open(filename, 'r', encoding="latin-1") as fh:
            started = False
            last = ""
            lineno = 0
            for line in fh:
                line = line.rstrip()
                lineno += 1
                if re.match(r'^\s*//\s*dist-ast-style-sort', line):
                    started = True
                if not started:
                    continue
                func = None
                # Constructor/destructor?
                m = re.match(r'^(([A-Z][A-Za-z0-9_]+)::~?\2)', line)
                if m:
                    func = m.group(1)
                else:
                    # Hack to handle pair<..., ...>
                    line = re.sub(r'(<[^>]+,) +([^>]+)>', r'\1\2', line)
                    # Function definitions
                    m = re.match(r'^(const\s+)?[a-zA-Z0-9_]\S+\s+([a-zA-Z0-9_]\S+)', line)
                    if m:
                        func = m.group(2)
                        if test.verbose:
                            print("- func: " + func)

                if func:
                    if func < last:
                        test.error_keep_going(filename + ":" + str(lineno) + ": Function '" +
                                              func +
                                              "' in incorrect sort-by-function-name position")
                    else:
                        last = func
                elif re.match(r'^[a-zA-Z_]', line):
                    test.error_keep_going(filename + ":" + str(lineno) + ": Unexpected line: " +
                                          line)

            if not started:
                test.error("Missing a dist-ast-style-start metacomment")


#            test.error_keep_going(k['fileline'] + ": Member '" + k['dtype'] + " " + k['key'] +
#                                  "' is declared but not printed in " + missings)

if not os.path.exists(test.root + "/.git"):
    test.skip("Not in a git repository")

read_ast_nodes_cpp()

test.passes()
