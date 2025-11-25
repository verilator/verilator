#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_lib_prot.v"
if test.benchmark:
    test.sim_time = test.benchmark * 100

trace_opt = "" if re.search(r'--no-trace', ' '.join(test.driver_verilator_flags)) else "-trace"

secret_prefix = "secret"
secret_dir = test.obj_dir + "/" + secret_prefix
test.mkdir_ok(secret_dir)

# Compile the lib
test.run(logfile=secret_dir + "/vlt_compile.log",
         cmd=[
             "perl", os.environ["VERILATOR_ROOT"] + "/bin/verilator", '--no-timing', "--prof-exec",
             trace_opt, "--prefix", "Vt_lib_prot_secret", "-cc", "-Mdir", secret_dir,
             "--lib-create", secret_prefix, "t/t_lib_prot_secret.v"
         ],
         verilator_run=True)
test.run(logfile=secret_dir + "/secret_gcc.log",
         cmd=[os.environ["MAKE"], "-C", secret_dir, "-f", "Vt_lib_prot_secret.mk"])

# Compile the simulator
test.compile(verilator_flags2=[
    '--no-timing', "--prof-exec", trace_opt, "-LDFLAGS", secret_prefix +
    "/libsecret.a", secret_dir + "/secret.sv"
])

# Run with profiling
test.execute(all_run_flags=[
    "+verilator+prof+exec+start+0", " +verilator+prof+exec+window+10",
    " +verilator+prof+exec+file+" + test.obj_dir + "/profile_exec.dat"
])

# Generate report
gantt_log = test.obj_dir + "/gantt.log"
test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_gantt", test.obj_dir +
    "/profile_exec.dat", "--vcd " + test.obj_dir + "/profile_exec.vcd", "| tee " + gantt_log
])

# Check both lib and sim are present
test.file_grep(gantt_log, r'\|\s+[1-9][0-9]*\s+\|\s+[0-9.]+\s+\|\s+eval')
test.file_grep(gantt_log, r'\|\s+[1-9][0-9]*\s+\|\s+[0-9.]+\s+\|\s+secret:eval')

test.passes()
