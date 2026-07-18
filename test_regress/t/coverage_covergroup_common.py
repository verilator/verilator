# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re


def covergroup_coverage_report(test, outfile=None):
    """Parse coverage.dat and write a sorted covergroup bin hit-count report.

    Lines have the form:  <hierarchy>[  [bin_type]]: <count>
    ignore_bins and illegal_bins are annotated with [ignore] / [illegal].

    Returns the path to the written report file.
    """
    if outfile is None:
        outfile = test.obj_dir + "/covergroup_report.txt"
    contents = test.file_contents(test.coverage_filename)
    entries = []
    for m in re.finditer(r"C '([^']+)' (\d+)", contents):
        entry, count = m.group(1), m.group(2)
        if '\x01t\x02covergroup' not in entry:
            continue
        h_m = re.search(r'\x01h\x02([^\x01]+)', entry)
        if not h_m:
            continue
        hier = h_m.group(1)
        bt_m = re.search(r'\x01bin_type\x02([^\x01]+)', entry)
        cross_m = re.search(r'\x01cross\x021', entry)
        annotations = []
        if bt_m:
            annotations.append(bt_m.group(1))
        if cross_m:
            annotations.append("cross")
        label = f"{hier} [{','.join(annotations)}]" if annotations else hier
        entries.append((hier, label, int(count)))
    entries.sort()
    with open(outfile, 'w', encoding='utf-8') as fh:
        for _hier, label, count in entries:
            fh.write(f"{label}: {count}\n")
    return outfile


def run(test, *, verilator_flags2=()):
    test.compile(verilator_flags2=['--coverage', *verilator_flags2])
    test.execute()
    covergroup_coverage_report(test)
    test.files_identical(test.obj_dir + '/covergroup_report.txt', test.golden_filename)
    test.passes()
