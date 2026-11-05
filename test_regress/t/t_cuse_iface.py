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

test.compile(verilator_flags2=["-fno-inline"])

# The header holding the virtual interface handle declares the interface class
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "_sub.h",
               r'^class ' + test.vm_prefix + r'_ifc;$')

test.execute()

test.passes()
