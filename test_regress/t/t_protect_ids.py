#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

# Use --debug-protect to assist debug

# This test makes randomly named .cpp/.h files, which tend to collect, so remove them first
for filename in (glob.glob(test.obj_dir + "/*_PS*.cpp") + glob.glob(test.obj_dir + "/*_PS*.h") +
                 glob.glob(test.obj_dir + "/*.d")):
    test.unlink_ok(filename)

test.compile(verilator_flags2=[
    "--protect-ids", "--protect-key SECRET_KEY", "--trace-vcd", "--coverage", "-Wno-INSECURE",
    "t/t_protect_ids_c.cpp"
])

test.execute()

# 'to="PS"' indicates means we probably mis-protected something already protected
# Use --debug-protect to assist debugging these
test.file_grep_not(test.obj_dir + "/" + test.vm_prefix + "__idmap.xml", r'to="PS')

if test.vlt_all:
    # Check for secret in any outputs
    for filename in test.glob_some(test.obj_dir + "/*.[ch]*"):
        if re.search(r'secret', filename, re.IGNORECASE):
            test.error("Secret found in a filename: " + filename)
        test.file_grep_not(filename, r'secret')

test.passes()
