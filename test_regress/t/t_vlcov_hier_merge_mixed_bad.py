#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re

import vltest_bootstrap

test.scenarios('simulator')

if not test.have_coroutines:
    test.skip("Test requires Coroutines; ignore error since not available")

hier_dir = test.obj_dir + "/hier"
flat_dir = test.obj_dir + "/flat"
hier_cov = hier_dir + "/coverage.dat"
flat_cov = flat_dir + "/coverage.dat"
source = "t/t_vlcov_hier_report_runtime.v"

test.mkdir_ok(hier_dir)
test.mkdir_ok(flat_dir)

common_compile = [
    "perl",
    os.environ["VERILATOR_ROOT"] + "/bin/verilator",
    "--binary",
    "--coverage",
    "--coverage-fsm",
    "--top-module",
    "tb",
    "--timing",
    source,
]

test.run(cmd=[
    *common_compile,
    "--prefix",
    "Vhier",
    "-Mdir",
    hier_dir,
    "--coverage-per-instance",
],
         logfile=test.obj_dir + "/vlt_compile_hier.log",
         verilator_run=True)

test.run(cmd=[
    hier_dir + "/Vhier",
    "+verilator+coverage+file+" + hier_cov,
],
         logfile=test.obj_dir + "/vlt_sim_hier.log",
         check_finished=True,
         verilator_run=True)

test.run(cmd=[
    *common_compile,
    "--prefix",
    "Vflat",
    "-Mdir",
    flat_dir,
],
         logfile=test.obj_dir + "/vlt_compile_flat.log",
         verilator_run=True)

test.run(cmd=[
    flat_dir + "/Vflat",
    "+verilator+coverage+file+" + flat_cov,
],
         logfile=test.obj_dir + "/vlt_sim_flat.log",
         check_finished=True,
         verilator_run=True)

test.run(cmd=[
    "cd",
    test.obj_dir,
    "&&",
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--hier-merge",
    "--write",
    "coverage.dat",
    "hier/coverage.dat",
    "flat/coverage.dat",
],
         logfile=test.run_log_filename,
         fails=True,
         verilator_run=True)

normalized = test.obj_dir + "/vlcov_normalized.log"
with open(test.run_log_filename) as in_fh:
    text = in_fh.read()
text = re.sub(r"verilator_doc[.]html[?]v=[^ ]+", "verilator_doc.html?v=latest", text)
with open(normalized, "w") as out_fh:
    out_fh.write(text)

test.files_identical(normalized, test.golden_filename)

test.passes()
