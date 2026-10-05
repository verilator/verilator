#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# Otherwise a rerun skips the unchanged plan, and so the failing final Verilation
test.clean_objs()

# Reported when the final Verilation, run by make, looks up the libraries
test.compile(verilator_flags2=['--hierarchical'], fails='any')

for line in (19, 21):
    test.file_grep(
        test.compile_log_filename,
        r"%Error-UNSUPPORTED: t/t_hier_block_param_kind_unsup.v:" + str(line) +
        r":10: Unsupported: Untyped parameter 'P' of hierarchical block 'mid' given equal values of different width or signedness"
    )

test.passes()
