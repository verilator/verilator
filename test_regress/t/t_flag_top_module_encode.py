#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# Cannot use compile as want to not get --prefix
test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator", '--cc', '--Mdir', test.obj_dir,
    '--top-module', '"a:b__c"', test.top_filename
],
         verilator_run=True)

for filename in test.glob_some(test.obj_dir + "/*.h"):
    test.file_grep_not(filename, r'__05F03ab___05F_05Fc')
    #test.file_grep(filename, r'dly__t__DOT__v1')

test.passes()
