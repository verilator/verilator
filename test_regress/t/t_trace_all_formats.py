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
test.top_filename = "t/t_trace_complex.v"

# Trace in all formats at the same time.
# Verilated for FST, which links its libraries, adding the VCD and SAIF runtimes.
test.compile(verilator_flags2=[
    "--cc --exe --trace-fst", test.pli_filename, "verilated_vcd_c.cpp", "verilated_saif_c.cpp"
],
             make_top_shell=False,
             make_main=False)

test.execute()

# Must match tests tracing the same formats individually
test.trace_identical(test.obj_dir + "/simx.vcd", "t/t_trace_complex_default_cc_vcd.out")
test.trace_identical(test.obj_dir + "/simx.fst", "t/t_trace_complex_default_cc_fst.out")
test.trace_identical(test.obj_dir + "/simx.saif", "t/t_trace_complex_default_cc_saif.out")

test.passes()
