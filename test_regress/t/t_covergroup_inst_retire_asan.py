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
test.top_filename = 't/t_covergroup_inst_retire.v'

# A wrong erase-by-swap frees the wrong node and leaves the right one orphaned.
# The plain run catches that through the live count; this catches it as the
# use-after-free it also is, and catches the orphan as a leak at exit.
#
# AddressSanitizer only, not --runtime-debug: its -fsanitize=undefined and
# -D_GLIBCXX_DEBUG add nothing to a lifetime test and triple the runtime
# recompile.  ASAN is incompatible with TSAN, which --runtime-debug would have
# made driver.py notice for us.
if test.tsan:
    test.skip("ThreadSanitizer not compatible with AddressSanitizer\n")

test.compile(verilator_flags2=[
    "-CFLAGS -fsanitize=address -CFLAGS -ggdb"
    " -LDFLAGS -fsanitize=address -LDFLAGS -ggdb"
])

test.execute()

test.passes()
