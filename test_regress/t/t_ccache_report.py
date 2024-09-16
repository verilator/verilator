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
test.top_filename = "t_a1_first_cc.v"

if not test.cfg_with_ccache:
    test.skip("Requires configuring with ccache")

# This test requires rebuilding the object files to check the ccache log
for filename in glob.glob(test.obj_dir + "/*.o"):
    test.unlink_ok(filename)

test.compile(verilator_flags2=['--trace'], make_flags=["ccache-report"])

report = test.obj_dir + "/" + test.vm_prefix + "__ccache_report.txt"

# We do not actually want to make this test depend on whether the file was
# cached or not, so trim the report to ignore actual caching behaviour
test.run(cmd=["sed", "-i", "-e", "'s/ : .*/ : IGNORED/; /|/s/.*/IGNORED/;'", report])
test.files_identical(report, "t/" + test.name + "__ccache_report_initial.out")

# Now rebuild again (should be all up to date)
test.run(logfile=test.obj_dir + "/rebuild.log",
         cmd=[
             "make", "-C " + test.obj_dir, "-f " + test.vm_prefix + ".mk", test.vm_prefix,
             "ccache-report"
         ])

test.files_identical(report, "t/" + test.name + "__ccache_report_rebuild.out")

test.passes()
