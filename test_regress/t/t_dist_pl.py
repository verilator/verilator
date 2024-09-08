#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

root = ".."

for pl in sorted(test.glob_some(root + "/test_regress/t/*.pl")):
    if 'bootstrap.pl' in pl:
        continue
    py = re.sub(r'\.pl', '.py', pl)
    test.error_keep_going(pl + ":1: Perl test needs conversion into a Python test '" +
                          os.path.basename(py) + "'")

test.passes()
