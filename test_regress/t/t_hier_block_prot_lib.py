#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all', 'xsim')
test.top_filename = "t/t_hier_block.v"

secret_prefix = "secret"
secret_dir = test.obj_dir + "/" + secret_prefix
test.mkdir_ok(secret_dir)

# Always compile the secret file with Verilator no matter what simulator
#   we are testing with
test.run(logfile=secret_dir + "/vlt_compile.log",
         cmd=[
             "perl", os.environ["VERILATOR_ROOT"] + "/bin/verilator", "-cc", "--hierarchical",
             "-Mdir", secret_dir, "--protect-lib", secret_prefix, "--protect-key", "PROTECT_KEY",
             "t/t_hier_block.v", "-DAS_PROT_LIB", '--CFLAGS', '"-pipe -DCPP_MACRO=cplusplus"',
             (' --threads 1' if test.vltmt else ''), "--build"
         ],
         verilator_run=True)

test.compile(v_flags2=['t/t_hier_block.cpp'],
             verilator_flags2=[
                 secret_dir + "/secret.sv", "-DPROTLIB_TOP", "--top-module t", "-LDFLAGS",
                 "'" + secret_prefix + "/libsecret.a'"
             ])

test.execute()

test.passes()

test.file_grep(secret_dir + "/Vsub0/sub0.sv", r'^module\s+(\S+)\s+', "sub0")
test.file_grep(secret_dir + "/Vsub1/sub1.sv", r'^module\s+(\S+)\s+', "sub1")
test.file_grep(secret_dir + "/Vsub2/sub2.sv", r'^module\s+(\S+)\s+', "sub2")
test.file_grep(test.run_log_filename, r'MACRO:(\S+) is defined', "cplusplus")

test.passes()
