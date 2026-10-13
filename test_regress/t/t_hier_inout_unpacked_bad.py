#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

# Recreate the plan so a rerun still launches the failing child Verilation.
test.clean_objs()
test.compile(fails='any', verilator_flags2=['--hierarchical'])

# Omit make's commands and absolute directory paths before the diagnostics.
diagnostics = re.sub(r'\A.*?(?=%Error:)',
                     '',
                     test.file_contents(test.compile_log_filename),
                     flags=re.S)
logfile = test.obj_dir + '/diagnostics.log'
test.write_wholefile(logfile, diagnostics)
test.files_identical(logfile, test.golden_filename, is_logfile=True)

test.passes()
