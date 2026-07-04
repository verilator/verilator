#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# Without --timing, an embedded covergroup clocked on (or otherwise referencing) an
# enclosing-class member cannot be fully supported: dynamic per-instance event waits are
# unavailable.  Verilator emits a clean COVERIGN warning for each such limitation.  With
# --timing these same covergroups are fully supported (see t_covergroup_embedded_timing).
test.lint(verilator_flags2=['--no-timing'], expect_filename=test.golden_filename, fails=True)

test.passes()
