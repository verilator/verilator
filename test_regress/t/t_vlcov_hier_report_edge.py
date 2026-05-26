#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

edge_cov = test.obj_dir + "/edge.dat"
no_du_cov = test.obj_dir + "/no_du.dat"
with open(edge_cov, "w", encoding="utf-8") as fh:
    fh.write("# SystemC::Coverage-3\n")
    # Exercise hierarchy-report edge cases that are awkward to generate from a
    # normal Verilated model but still need stable consumer behavior.  Use
    # SoC-like hierarchy names and mixed hit/miss records to keep the expected
    # report readable while covering the parser edge paths.
    # Malformed encoded keys exercise both parser paths that skip text before a
    # key marker and stop at a missing key/value separator.
    fh.write("C 'junk\001bad' 1\n")
    # Well-formed record without hier: skipped by hierarchy reporting.
    fh.write("C '\001f\002t/soc.v\001l\0021\001t\002line\001page\002v_line/core' 11\n")
    # Page without slash: design-unit name is the full page.  Use several
    # mixed hit/miss records so the expected report exercises non-trivial
    # percentages and varied totals instead of only 1/2 buckets.
    fh.write("C '\001f\002t/soc.v\001l\00220\001t\002line\001page\002bare_design"
             "\001h\002tb.cluster1..u_core' 37\n")
    fh.write("C '\001f\002t/soc.v\001l\00221\001t\002line\001page\002bare_design"
             "\001h\002tb.cluster1..u_core' 0\n")
    fh.write("C '\001f\002t/soc.v\001l\00222\001t\002line\001page\002bare_design"
             "\001h\002tb.cluster1..u_core' 4\n")
    fh.write("C '\001f\002t/soc.v\001l\00223\001t\002line\001page\002bare_design"
             "\001h\002tb.cluster1..u_core' 0\n")
    # Empty page: hierarchy prints, but design-unit tally remains empty for this point.
    fh.write("C '\001f\002t/soc.v\001l\00230\001t\002toggle\001h\002tb.unscoped_probe' 0\n")
    fh.write("C '\001f\002t/soc.v\001l\00231\001t\002toggle\001h\002tb.unscoped_probe' 18\n")
    fh.write("C '\001f\002t/soc.v\001l\00232\001t\002toggle\001h\002tb.unscoped_probe' 2\n")
    # Question-mark collapsed hierarchy: warning path distinct from star globs.
    fh.write("C '\001f\002t/soc.v\001l\00240\001t\002branch\001page\002v_branch/core"
             "\001h\002tb.cluster0.u_core?' 0\n")
    fh.write("C '\001f\002t/soc.v\001l\00241\001t\002branch\001page\002v_branch/core"
             "\001h\002tb.cluster0.u_core?' 29\n")
    fh.write("C '\001f\002t/soc.v\001l\00242\001t\002branch\001page\002v_branch/core"
             "\001h\002tb.cluster0.u_core?' 0\n")
    fh.write("C '\001f\002t/soc.v\001l\00243\001t\002branch\001page\002v_branch/core"
             "\001h\002tb.cluster0.u_core?' 6\n")
    fh.write("C '\001f\002t/soc.v\001l\00244\001t\002branch\001page\002v_branch/core"
             "\001h\002tb.cluster0.u_core?' 1\n")
    # Trailing dots are ignored after the final hierarchy component.
    fh.write("C '\001f\002t/soc.v\001l\00245\001t\002expr\001page\002v_expr/trailing"
             "\001h\002tb.trailing.' 5\n")

with open(no_du_cov, "w", encoding="utf-8") as fh:
    fh.write("# SystemC::Coverage-3\n")
    # A separate hierarchy report with only empty-page records exercises the
    # path where no design-unit summary is printed.
    fh.write("C '\001f\002t/soc.v\001l\00250\001t\002toggle\001h\002tb.unscoped_only' 0\n")
    fh.write("C '\001f\002t/soc.v\001l\00251\001t\002toggle\001h\002tb.unscoped_only' 7\n")
    fh.write("C '\001f\002t/soc.v\001l\00252\001t\002toggle\001h\002tb.unscoped_only' 0\n")
    fh.write("C '\001f\002t/soc.v\001l\00253\001t\002toggle\001h\002tb.unscoped_only' 1\n")

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--report",
    "hierarchy",
    edge_cov,
],
         logfile=test.obj_dir + "/edge.log",
         tee=False,
         verilator_run=True)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--report",
    "hierarchy",
    no_du_cov,
],
         logfile=test.obj_dir + "/no_du.log",
         tee=False,
         verilator_run=True)

combined_log = test.obj_dir + "/vlcov.log"
with open(combined_log, "w", encoding="utf-8") as out:
    out.write("$ verilator_coverage --report hierarchy edge.dat\n")
    with open(test.obj_dir + "/edge.log", encoding="utf-8") as fh:
        out.write(fh.read())
    out.write("\n$ verilator_coverage --report hierarchy no_du.dat\n")
    with open(test.obj_dir + "/no_du.log", encoding="utf-8") as fh:
        out.write(fh.read())

test.files_identical(combined_log, test.golden_filename)

test.passes()
