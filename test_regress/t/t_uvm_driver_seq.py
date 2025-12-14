#!/usr/bin/env python3
# DESCRIPTION: Verilator: Minimal UVM driver/sequence example
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2025 by Verilator Authors.
# SPDX-License-Identifier: CC0-1.0

import vltest_bootstrap

test.scenarios('vlt')

if test.have_dev_gcov:
    test.skip("Test suite intended for full dev coverage without needing this test")

test.compile(v_flags2=[
    "--binary",
    "-j 0",
    "--CFLAGS -O0",
    "-Wno-WIDTHTRUNC",
    "-Wno-WIDTHEXPAND",
    "-Wno-UNUSEDSIGNAL",
    "-Wno-IMPORTSTAR",
    "-Wno-DECLFILENAME",
    "+incdir+t/uvm",
    "t/uvm/uvm_pkg_all_v2020_3_1_nodpi.svh",
])

test.execute(all_run_flags=['' if test.verbose else '+UVM_NO_RELNOTES'])

test.file_grep(test.run_log_filename, r'\*-\* All Finished \*-\*')

test.passes()
