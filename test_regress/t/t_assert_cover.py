#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_assert_cover.v"

test.compile(verilator_flags2=['--assert --cc --coverage-user'],
             nc_flags2=["+nccovoverwrite +nccoverage+all +nccovtest+" + test.name])

test.execute()

if test.nc:
    cf = test.obj_dir + "/" + test.name + "__nccover.cf"

    with open(cf, 'w', encoding="utf8") as fh:
        fh.write("report_summary -module *\n")
        fh.write("report_detail -both -instance *\n")
        fh.write("report_html -both -instance * > " + test.obj_dir + "/" + test.name +
                 "__nccover.html\n")

    test.run(logfile=test.obj_dir + "/" + test.name + "__nccover.log",
             tee=False,
             cmd=[test.getenv_def("VERILATOR_ICCR", 'iccr'), "-test", test.name, cf])

test.file_grep(test.run_log_filename, r'COVER: Cyc==4')
test.file_grep(test.run_log_filename, r'COVER: Cyc==5')
test.file_grep(test.run_log_filename, r'COVER: Cyc==6')

# Allow old SystemC::Coverage format dump, or new binary dump
test.file_grep(test.coverage_filename, r'(cyc_eq_5.*,c=>[^0]|cyc_eq_5.* [1-9][0-9]*\n)')

test.passes()
