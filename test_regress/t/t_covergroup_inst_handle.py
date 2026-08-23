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

# Hand-written harness: neither property is reachable from SystemVerilog -- an
# attach count above 1 needs the handle's copy constructor, and a handle
# outliving the registry needs the context destroyed before the model.  See the
# .cpp.
#
# Built WITHOUT --coverage, so retirement is on the free path, and with
# AddressSanitizer: freeing a node under a live handle is a use-after-free that
# without a sanitizer is a segfault or a silent pass depending on the allocator.
# Not --runtime-debug: its extra checks add nothing here and triple the runtime
# recompile.  ASAN is incompatible with TSAN, which --runtime-debug would have
# made driver.py notice for us.
if test.tsan:
    test.skip("ThreadSanitizer not compatible with AddressSanitizer\n")

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe", "-CFLAGS -fsanitize=address -CFLAGS -ggdb"
                 " -LDFLAGS -fsanitize=address -LDFLAGS -ggdb", test.pli_filename
             ])

# LeakSanitizer off: this test leaks on purpose -- the registry leaks the type it
# may not free, the harness leaks the model it must not delete.  Both are the
# subject of the test.  Every other check, use-after-free included, stays on.
test.leak_check_disable()

test.execute()

test.passes()
