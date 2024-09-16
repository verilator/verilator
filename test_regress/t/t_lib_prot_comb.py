#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all', 'xsim')

if test.benchmark:
    test.sim_time = test.benchmark * 100

trace_opt = ""

secret_prefix = "secret"
secret_dir = test.obj_dir + "/" + secret_prefix
test.mkdir_ok(secret_dir)

# Always compile the secret file with Verilator no matter what simulator
#   we are testing with
test.run(
    logfile=secret_dir + "/vlt_compile.log",
    cmd=["perl", os.environ["VERILATOR_ROOT"] + "/bin/verilator",
         "-cc",
         trace_opt,
         "--prefix", "Vt_lib_prot_secret",
         "-Mdir", secret_dir,
         "--protect-lib", secret_prefix,
         "--protect-key", "secret-key",
         "t/t_lib_prot_comb.v"],
    verilator_run=True)  # yapf:disable

test.run(logfile=secret_dir + "/secret_gcc.log",
         cmd=[os.environ["MAKE"], "-C", secret_dir, "-f", "Vt_lib_prot_secret.mk"])

test.compile(
    verilator_flags2=[
        secret_dir + "/secret.sv",
        "+define+PROCESS_TOP",
        "-LDFLAGS",secret_prefix + "/libsecret.a"],
    xsim_flags2=[secret_dir + "/secret.sv"])  # yapf:disable

test.execute(xsim_run_flags2=["--sv_lib", secret_dir + "/libsecret", "--dpi_absolute"])

test.passes()
