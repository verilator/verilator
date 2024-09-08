#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')
test.top_filename = "t/t_gen_alw.v"  # It doesn't really matter what test

test.compile(v_flags2=["--prof-pgo"], threads=2)

test.execute(all_run_flags=[
    "+verilator+prof+exec+start+0",
    " +verilator+prof+exec+file+/dev/null",
    " +verilator+prof+vlt+file+" + test.obj_dir + "/profile.vlt"])  # yapf:disable

test.file_grep(test.obj_dir + "/profile.vlt", r'profile_data ')

test.compile(
    # Intentionally no --prof-pgo here to make sure profile data can be read in
    # without it (that is: --prof-pgo has no effect on profile_data hash names)
    v_flags2=[" " + test.obj_dir + "/profile.vlt"],
    threads=2)

test.execute()

test.passes()
