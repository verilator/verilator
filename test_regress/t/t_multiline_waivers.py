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

out_filename = test.obj_dir + "/" + test.name + "_waiver_gen.vlt"
waiver_filename = test.obj_dir + "/" + test.name + "_waiver.vlt"

test.compile(v_flags2=['--waiver-output', out_filename], fails=True)

test.file_sed(out_filename, waiver_filename,
              lambda line: re.sub(r'\/\/ lint_off', 'lint_off', line))

test.compile(v_flags2=[waiver_filename])

test.passes()
