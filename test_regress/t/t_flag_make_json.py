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
test.top_filename = "t/t_flag_make_cmake.v"

test.compile(verilator_flags2=['--make json'],
             verilator_make_gmake=False,
             verilator_make_cmake=False)

nout = test.run_capture("jq --version", check=False)
version_match = re.search(r'jq-([0-9.]+)', nout, re.IGNORECASE)
if not version_match:
    test.skip("jq is not installed")

json_filename = test.obj_dir + "/" + test.vm_prefix + ".json"
if not os.path.exists(json_filename):
    test.error(json_filename + " does not exist")

test.run(cmd=['cat "' + json_filename + '" | jq ".version"'])

test.passes()
