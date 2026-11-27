#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

from pathlib import Path

import vltest_bootstrap
from assert_ctl_arg import check_output

test.scenarios('vlt_all')
test.top_filename = 't/t_assert_ctl_arg.v'
threads = 2 if test.vltmt else 1
driver = Path(test.obj_dir) / 'driver.cpp'
driver.write_text(Path('t/t_assert_ctl_arg.cpp').read_text(encoding="utf8").replace(
    'contextp->threads(1);', f'contextp->threads({threads});'),
                  encoding="utf8")

# The concurrent submodule has two permanently zero coverage bins. Its
# clocked state can move into RepCut kernels, but its coverage scope must remain.
test.compile(make_top_shell=False,
             make_main=False,
             threads=threads,
             verilator_flags2=[
                 '-frepcut', '--assert', '--timing', '--coverage-user', '-fno-inline', '--exe',
                 str(driver.resolve()), '-CFLAGS', '-I' + str(Path('t').resolve())
             ])
test.execute(all_run_flags=['+verilator+error+limit+100'])

check_output(test, test.t_dir + '/t_assert_ctl_arg.out')
test.files_identical(test.coverage_filename, 't/t_assert_ctl_arg.dat.out')
test.passes()
