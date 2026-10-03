#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.top_filename = "t/t_covergroup_cross.v"

# --Wno-ASCRANGE: cg_be / cg_be_arr in the shared top intentionally declare ascending [0:N]
test.compile(verilator_flags2=['--coverage', '--Wno-COVERIGN', '--Wno-ASCRANGE'])

test.execute()

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate",
    test.obj_dir + "/annotated",
    "--annotate-points",
    test.obj_dir + "/coverage.dat",
],
         verilator_run=True)

test.files_identical(test.obj_dir + "/annotated/t_covergroup_cross.v",
                     "t/" + test.name + ".annotate.out")

# A bin's option.at_least is its threshold ('s') in the coverage database
test.file_grep(test.obj_dir + "/coverage.dat", r"\x01s\x023\x01h\x02cg_at_least\.addr_cmd_al\.")

# Ranking counts a test as covering a bin once its hits reach the bin's threshold
thresh_dat = test.obj_dir + "/thresh.dat"
with open(thresh_dat, "w", encoding="utf-8") as fh:
    fh.write("# SystemC::Coverage-3\n")
    for (bin_name, thresh, count) in (
        ("lo", "2", 2),
        ("mid", "2", 1),
        ("hi", "", 1),
        ("any", "0", 0),
    ):
        fh.write("C '\001t\002covergroup\001page\002v_covergroup/cg\001f\002t.v\001l\0021" +
                 ("\001s\002" + thresh if thresh else "") + "\001h\002cg.cp." + bin_name + "' " +
                 str(count) + "\n")
vlcov = os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage"
test.run(cmd=[vlcov, "--rank", thresh_dat], logfile=test.obj_dir + "/rank.log", verilator_run=True)
# lo and hi; no test covers any, as its threshold is not a hit
test.file_grep(test.obj_dir + "/rank.log", r"^\s+2,\s+1,\s+2,")

test.passes()
