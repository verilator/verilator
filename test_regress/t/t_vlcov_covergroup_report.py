#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

from coverage_common import init_log, run_vlcov, vlcov_run_context

test.scenarios('vlt')

test.compile(verilator_flags2=['--coverage-user'])

test.execute()

log = test.obj_dir + "/vlcov.log"
tmp_log = test.obj_dir + "/vlcov.tmp"
init_log(log)
vlcov = vlcov_run_context(test, log, tmp_log)


def dat_line(fields, count):
    return "C '" + "".join("\001" + key + "\002" + value
                           for key, value in fields) + "' " + str(count) + "\n"


def write_dat(name, records, points=()):
    filename = test.obj_dir + "/" + name
    with open(filename, "w", encoding="utf-8") as fh:
        fh.write("# SystemC::Coverage-3\n")
        for group, item, bin_name, count, keys in records:
            fields = [("t", "covergroup"), ("page", "v_covergroup/" + group), ("f", "t/cg.v"),
                      ("l", "1")]
            fields += keys
            fields.append(("h", group + "." + item + "." + bin_name))
            fh.write(dat_line(fields, count))
        for kind, hier, lineno, count in points:
            fields = [("t", kind), ("page", "v_" + kind + "/t"), ("f", "t/t.v"), ("l", lineno),
                      ("h", hier)]
            fh.write(dat_line(fields, count))
    return filename


# Covergroups of dotted names under one node, of which one is named with the value of a string
# parameter holding a quote that a space follows, as is the count, and one named with the values of
# the parameters of a specialization, whose dots split the name into no nodes, nor do the escaped
# quote and parenthesis of a string value, quoted as the coverage file quotes it; a record
# without its bin's name; records of a bin with different weights and thresholds, which merge with
# the largest of those; and records of two bins of a name, as of covergroups of distinct scopes
# that share a name, which do not merge
edge_cov = write_dat("edge.dat", [
    ("pkg.alpha", "cp", "b0", 1, [("B", "b0")]),
    ("pkg.alpha", "cp", "b1", 0, [("B", "b1")]),
    ("pkg.beta", "cp", "b0", 1, []),
    ('pkg.quote#("it\' s")', "cp", "b0", 0, [("B", "b0")]),
    ('pkg.Cls#(0.1,%22a.\\%22(b%22,class pkg::Inner#(1.5),2.5).cg', "cp", "b0", 1, [("B", "b0")]),
    ("split", "cp", "b0", 1, [("B", "b0"), ("s", "2"), ("w", "2")]),
    ("split", "cp", "b0", 0, [("B", "b0"), ("w", "3")]),
    ("split", "cq", "b0", 1, [("B", "b0")]),
    ("shared", "cp", "b0", 1, [("B", "b0"), ("n", "3")]),
    ("shared", "cp", "b0", 0, [("B", "b0"), ("n", "5")]),
])
# Covergroups of zero weight only: 100
zero_cov = write_dat("zero.dat", [("idle", "cp", "b0", 0, [("B", "b0"), ("Gw", "0")])])
# Covergroups without coverable bins only: 0
none_cov = write_dat("none.dat", [("void", "cp", "b0", 0, [("B", "b0"), ("Bt", "ignore")])])
# Coverage that is not complete shows below 100%: 99.95 as 99.9
near_cov = write_dat("near.dat", [("near", "cp", "b" + str(i), int(i != 0), [("B", "b" + str(i))])
                                  for i in range(2001)])
# A module shows a row per coverage type under its name; covergroups show one line each
mixed_cov = write_dat("mixed.dat", [("cg", "cp", "a", 1, [("B", "a")]),
                                    ("cg", "cp", "b", 0, [("B", "b")])],
                      points=[("line", "top.t", "10", 1), ("toggle", "top.t", "11", 0)])

run_vlcov(vlcov,
          "verilator_coverage --report summary,hierarchy coverage.dat",
          args=["--report", "summary,hierarchy", test.obj_dir + "/coverage.dat"])
run_vlcov(vlcov,
          "verilator_coverage --report summary,hierarchy edge.dat",
          args=["--report", "summary,hierarchy", edge_cov])
run_vlcov(vlcov,
          "verilator_coverage --report summary zero.dat",
          args=["--report", "summary", zero_cov])
run_vlcov(vlcov,
          "verilator_coverage --report summary none.dat",
          args=["--report", "summary", none_cov])
run_vlcov(vlcov,
          "verilator_coverage --report summary near.dat",
          args=["--report", "summary", near_cov])
run_vlcov(vlcov,
          "verilator_coverage --report hierarchy mixed.dat",
          args=["--report", "hierarchy", mixed_cov])
run_vlcov(vlcov,
          "verilator_coverage --report hierarchy --levels 1 mixed.dat",
          args=["--report", "hierarchy", "--levels", "1", mixed_cov])

test.files_identical(log, test.golden_filename)

test.passes()
