#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

# Only Verilator links the poisoning allocator into the simulation
test.scenarios('vlt')

secret_prefix = "secret"
secret_dir = test.obj_dir + "/" + secret_prefix
test.mkdir_ok(secret_dir)

test.run(
    logfile=secret_dir + "/vlt_compile.log",
    cmd=["perl", os.environ["VERILATOR_ROOT"] + "/bin/verilator",
         "-cc",
         "--prefix", "Vt_lib_prot_secret",
         "-Mdir", secret_dir,
         "--protect-lib", secret_prefix,
         "--protect-key", "secret-key",
         test.top_filename],
    verilator_run=True)  # yapf:disable

test.run(logfile=secret_dir + "/secret_gcc.log",
         cmd=[os.environ["MAKE"], "-C", secret_dir, "-f", "Vt_lib_prot_secret.mk"])

test.compile(
    verilator_flags2=[
        secret_dir + "/secret.sv",
        "+define+PROCESS_TOP",
        test.pli_filename,
        "-LDFLAGS", secret_prefix + "/libsecret.a"])  # yapf:disable

test.execute()

test.passes()
