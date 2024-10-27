#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=["--protect-lib", "secret", "--protect-key", "SECRET_FAKE_KEY"],
             verilator_make_gcc=False,
             verilator_make_gmake=False,
             make_main=False,
             make_top_shell=False)

test.run(cmd=[os.environ["MAKE"], "-C", test.obj_dir, "-f", "V" + test.name + ".mk"])

test.passes()
