#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t_prof.v"

test.compile(verilator_flags2=["--stats --prof-c +define+T_PROF"])

# TODO below might no longer be required as configure checks for -pg
if 'VERILATOR_TEST_NO_GPROF' in os.environ:
    test.skip("Skipping due to VERILATOR_TEST_NO_GPROF")

for filename in glob.glob(test.obj_dir + "/gmon.out.*"):
    test.unlink_ok(filename)
test.setenv('GMON_OUT_PREFIX', test.obj_dir + "/gmon.out")

test.execute()

gmon_path = None
for filename in glob.glob(test.obj_dir + "/gmon.out.*"):
    gmon_path = filename
if not gmon_path:
    test.error("Profiler did not create a gmon.out")
gmon_base = re.sub(r'.*[/\\]', '', gmon_path)

test.run(
    cmd=["cd " + test.obj_dir + " && gprof " + test.vm_prefix + " " + gmon_base + " > gprof.log"],
    check_finished=False)

test.passes()
