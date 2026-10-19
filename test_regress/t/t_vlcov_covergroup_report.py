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


# A value of a record, escaped as the Verilated model escapes it, VerilatedCovKey::escape()
def escape(text):
    return "".join(c if " " <= c <= "~" and c not in '%"' else "%%%02X" % ord(c) for c in text)


def dat_line(fields, count):
    return "C '" + "".join("\001" + key + "\002" + escape(value)
                           for key, value in fields) + "' " + str(count) + "\n"


# The fields of the record of a covergroup's bin, with the given keys, by default at t/cg.v:1
def bin_fields(group, item, bin_name, keys):
    given = dict(keys)
    fields = [("t", "covergroup"), ("page", "v_covergroup/" + group),
              ("f", given.pop("f", "t/cg.v")), ("l", given.pop("l", "1"))]
    fields += given.items()
    fields.append(("h", group + "." + item + "." + bin_name))
    return fields


# The fields of the record of a coverage point of another kind, as of a line
def point_fields(kind, unit, hier, lineno):
    return [("t", kind), ("page", "v_" + kind + "/" + unit), ("f", "t/t.v"), ("l", lineno),
            ("h", hier)]


def write_dat(name, records, points=()):
    filename = test.obj_dir + "/" + name
    with open(filename, "w", encoding="utf-8") as fh:
        fh.write("# SystemC::Coverage-3\n")
        for group, item, bin_name, count, keys in records:
            fh.write(dat_line(bin_fields(group, item, bin_name, keys), count))
        for kind, unit, hier, lineno, count in points:
            fh.write(dat_line(point_fields(kind, unit, hier, lineno), count))
    return filename


# Covergroups of dotted names under one node, of which one is named with the value of a string
# parameter holding a quote that a space follows, as is the count, and one named with the values of
# the parameters of a specialization, whose dots split the name into no nodes, nor do the escaped
# quote and parenthesis of a string value; covergroups of escaped identifiers, to the space ending
# each, whose dots, parentheses, and quotes split the names into no nodes; names whose
# identifiers, parentheses, or quotes do not end, as $typename writes none, which split at each
# dot; a record without its bin's name; records of a bin with different weights and thresholds,
# which merge with the largest of those; and records of two bins of a name, as of covergroups of
# distinct scopes that share a name, which do not merge
edge_cov = write_dat("edge.dat", [
    ("pkg.alpha", "cp", "b0", 1, [("B", "b0")]),
    ("pkg.alpha", "cp", "b1", 0, [("B", "b1")]),
    ("pkg.beta", "cp", "b0", 1, []),
    ('pkg.quote#("it\' s")', "cp", "b0", 0, [("B", "b0")]),
    ('pkg.Cls#(0.1,"a.\\"(b",class pkg::Inner#(1.5),2.5).cg', "cp", "b0", 1, [("B", "b0")]),
    ("esc.\\gen.cg ", "cp", "b0", 1, [("B", "b0")]),
    ('esc.\\g#("x .cg', "cp", "b0", 0, [("B", "b0")]),
    ("unbal.\\e.cg", "cp", "b0", 1, [("B", "b0")]),
    ("unbal.g#(.cg", "cp", "b0", 1, [("B", "b0")]),
    ('unbal.m#(e"x).cg', "cp", "b0", 0, [("B", "b0")]),
    ("split", "cp", "b0", 1, [("B", "b0"), ("s", "2"), ("w", "2")]),
    ("split", "cp", "b0", 0, [("B", "b0"), ("w", "3")]),
    ("split", "cq", "b0", 1, [("B", "b0")]),
    ("shared", "cp", "b0", 1, [("B", "b0"), ("n", "3")]),
    ("shared", "cp", "b0", 0, [("B", "b0"), ("n", "5")]),
])
# As another writer may write it, a '%' that begins no escape, which stays as it is
with open(edge_cov, "a", encoding="utf-8") as fh:
    raw_fields = [("t", "covergroup"), ("page", "v_covergroup/raw"), ("f", "t/cg.v"), ("l", "1"),
                  ("B", "%zz%"), ("h", "raw.cp.%zz%")]
    fh.write("C '" + "".join("\001" + key + "\002" + value for key, value in raw_fields) + "' 1\n")
# Covergroups of zero weight only: 100
zero_cov = write_dat("zero.dat", [("idle", "cp", "b0", 0, [("B", "b0"), ("Gw", "0")])])
# Covergroups without coverable bins only: 0
none_cov = write_dat("none.dat", [("void", "cp", "b0", 0, [("B", "b0"), ("Bt", "ignore")])])
# Coverage that is not complete shows below 100%: 99.95 as 99.9
near_cov = write_dat("near.dat", [("near", "cp", "b" + str(i), int(i != 0), [("B", "b" + str(i))])
                                  for i in range(2001)])
# A module shows a row per coverage type under its name; covergroups show one line each; and
# names show their quotes and '%', which the coverage file escapes, as instance '"q%"' of module
# 'm"x'
mixed_cov = write_dat("mixed.dat", [("cg", "cp", "a", 1, [("B", "a")]),
                                    ("cg", "cp", "b", 0, [("B", "b")])],
                      points=[("line", "t", "top.t", "10", 1), ("toggle", "t", "top.t", "11", 0),
                              ("line", 'm"x', 'top.t."q%"', "12", 1)])
# Records whose names hold characters the coverage file escapes, '"' and '%', and the text '%22',
# and characters of the names of types, '<', '#(', and '::', which each output shows as the design
# writes them, but for the coverage file --write writes, which keeps its escapes, so reads back
# the same; and a character that does not print, which stays escaped, so each output keeps its
# lines
names_v = test.obj_dir + "/names.v"
with open(names_v, "w", encoding="utf-8") as fh:
    fh.write("module names;\n  // sampled\nendmodule\n")
names_cg = 'pkg::Cls#("a%<b%22")::cg'
names_cov = write_dat("names.dat", [
    (names_cg, "x", "<p,q>", 1, [("f", names_v), ("l", "2"), ("B", "<p,q>"), ("C", "1"),
                                 ("Cb", "p,q"), ("o", '"x%"\n<p,q> #( ::')]),
    (names_cg, "x", "<p,r>", 0, [("f", names_v), ("l", "2"), ("B", "<p,r>"), ("C", "1"),
                                 ("Cb", "p,r"), ("o", '"x%" <p,r> #( ::')]),
])
names_info = test.obj_dir + "/names.info"
names_merged = test.obj_dir + "/merged.dat"
annotated = test.obj_dir + "/annotated"


# Log the content of a file an output wrote
def log_file(label, filename):
    with open(log, "a", encoding="utf-8") as log_fh, open(filename, encoding="utf-8") as in_fh:
        log_fh.write("\n$ cat " + label + "\n" + in_fh.read())


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
run_vlcov(vlcov,
          "verilator_coverage --report summary,hierarchy names.dat",
          args=["--report", "summary,hierarchy", names_cov])
run_vlcov(vlcov,
          "verilator_coverage --annotate annotated --annotate-all --annotate-points names.dat",
          args=["--annotate", annotated, "--annotate-all", "--annotate-points", names_cov])
log_file("annotated/names.v", annotated + "/names.v")
run_vlcov(vlcov,
          "verilator_coverage --write-info names.info names.dat",
          args=["--write-info", names_info, names_cov])
log_file("names.info", names_info)
run_vlcov(vlcov,
          "verilator_coverage --write merged.dat names.dat",
          args=["--write", names_merged, names_cov])
run_vlcov(vlcov,
          "verilator_coverage --report hierarchy merged.dat",
          args=["--report", "hierarchy", names_merged])

test.files_identical(log, test.golden_filename)

test.passes()
