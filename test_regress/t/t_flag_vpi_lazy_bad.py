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

# Every diagnostic here comes from notify() rather than the parse, so any design will do.
test.top_filename = "t/t_vpi_empty.v"

# --public-flat-rw + --vpi-lazy contradictory; lazy takes precedence.
test.lint(fails=True,
          verilator_flags2=["--vpi --vpi-lazy --public-flat-rw"],
          expect_filename=test.golden_filename)

# --vpi-lazy makes every signal and parameter VPI accessible, so subsumes these too
test.lint(fails=True,
          verilator_flags2=["--vpi-lazy --public-depth 1 --public-params"],
          expect_filename="t/t_flag_vpi_lazy_public_bad.out")

# --vpi-lazy implies --vpi, but must not silently reverse an explicit --no-vpi: it is ignored
# instead, suppressibly. Both orders, as the diagnostic comes from notify().
novpi_golden = "t/t_flag_vpi_lazy_novpi_bad.out"
test.lint(fails=True, verilator_flags2=["--vpi-lazy --no-vpi"], expect_filename=novpi_golden)
test.lint(fails=True, verilator_flags2=["--no-vpi --vpi-lazy"], expect_filename=novpi_golden)

# The INSECURE hint names --vpi-lazy, as removing only --vpi would leave VPI on
test.lint(fails=True,
          verilator_flags2=["--vpi --vpi-lazy --protect-ids"],
          expect_filename="t/t_flag_vpi_lazy_protect_bad.out")

# split_var on a variable only --vpi-lazy keeps must not blame 'public'
test.top_filename = "t/t_opt_bitblast_attr_bad.v"
test.compile(fails=True,
             verilator_flags2=["--vpi-lazy"],
             expect_filename="t/t_flag_vpi_lazy_splitvar_bad.out")

test.passes()
