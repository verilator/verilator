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

# Both diagnostics come from notify() rather than the parse, so any design will do.
test.top_filename = "t/t_vpi_empty.v"

# --public-flat-rw + --vpi-lazy contradictory; lazy takes precedence.
test.lint(fails=True,
          verilator_flags2=["--vpi --vpi-lazy --public-flat-rw"],
          expect_filename=test.golden_filename)

# --vpi-lazy implies --vpi, but must not silently reverse an explicit --no-vpi: it is ignored
# instead, suppressibly. Both orders, as the diagnostic comes from notify().
novpi_golden = "t/t_flag_vpi_lazy_novpi_bad.out"
test.lint(fails=True, verilator_flags2=["--vpi-lazy --no-vpi"], expect_filename=novpi_golden)
test.lint(fails=True, verilator_flags2=["--no-vpi --vpi-lazy"], expect_filename=novpi_golden)

# Suppressed, the warning is all that is given up: --no-vpi still wins, so the model is not a VPI
# model and none of the lazy passes run. Same design as t_flag_vpi_lazy_implicit, where
# --vpi-lazy alone does emit the scope rows.
test.top_filename = "t/t_vpi_lazy_xscope.v"

test.compile(verilator_flags2=["--vpi-lazy --no-vpi -Wno-NOEFFECT"])

test.file_grep(test.obj_dir + "/" + test.vm_prefix + "_classes.mk", r'VM_VPI = 0')
test.file_grep_not(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp",
                   r'VerilatedScope::SCOPE_MODULE')
test.file_grep_not(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp",
                   r'VLVF_LAZY_PUBLIC_RW')

test.passes()
