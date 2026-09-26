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

# The lazy tables are reachable only through VPI, so --vpi-lazy alone must build a VPI model
# rather than self-disabling. Same design and testbench as t_vpi_lazy_xscope, which passes
# --vpi explicitly.
test.top_filename = "t/t_vpi_lazy_xscope.v"
test.pli_filename = "t/t_vpi_lazy_xscope.cpp"

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=["--exe --vpi-lazy --no-l2name --stats", test.pli_filename])

# SCOPE_MODULE rows are emitted only for a VPI model; the lazy work is unchanged by the
# implication
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp",
               r'VerilatedScope::SCOPE_MODULE')
test.file_grep(test.stats, r'VPI, lazy cross-scope copy descriptors\s+(\d+)', 2)

test.execute()

test.passes()
