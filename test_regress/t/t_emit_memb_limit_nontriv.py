#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re

import vltest_bootstrap

test.scenarios('vlt')

LIMIT = 3

test.compile(verilator_flags2=["--comp-limit-members", str(LIMIT), "--vpi"])

test.execute()


# Return the largest number of members declared directly in one struct or union body
def max_members(filename):
    result = 0
    bodies = []  # Member count of each open body, None if not a struct or union
    with open(filename, 'r', encoding="utf8") as fh:
        for line in fh:
            line = line.strip()
            if line.endswith('{'):
                bodies.append(0 if re.match(r'(struct|union) \{$', line) else None)
            elif line.startswith('}'):
                bodies.pop()
                if bodies and bodies[-1] is not None:
                    bodies[-1] += 1  # A struct or union is a member of its parent
            elif bodies and bodies[-1] is not None and line.endswith(';'):
                bodies[-1] += 1
            if bodies and bodies[-1] is not None:
                result = max(result, bodies[-1])
    return result


root = test.obj_dir + "/" + test.vm_prefix + "___024root.h"
for header in [root] + test.glob_some(test.obj_dir + "/" + test.vm_prefix + "_sub__*.h"):
    if max_members(header) > LIMIT:
        test.error(header + ": struct or union with more than " + str(LIMIT) + " members")

# $root's 42 members are in 14 innermost, 5 middle and 2 outermost structs
test.file_grep_count(root, r'\} __Vg\d+;', 21)
# 20 members are in 7 innermost and 3 outer structs
test.file_grep_count(test.obj_dir + "/" + test.vm_prefix + "_sub__N14.h", r'\} __Vg\d+;', 10)
# 5 members are in 2 structs
test.file_grep_count(test.obj_dir + "/" + test.vm_prefix + "_sub__N5.h", r'\} __Vg\d+;', 2)
# 3 members are not nested
test.file_grep_count(test.obj_dir + "/" + test.vm_prefix + "_sub__N3.h", r'\} __Vg\d+;', 0)

test.passes()
