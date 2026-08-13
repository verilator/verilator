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

# Compile the cross-coverage design with --protect-ids and confirm the coverage
# database is obfuscated like line/toggle points: none of the "cgsecret"-marked
# covergroup/coverpoint/cross/bin names, nor the source filename, may leak into
# coverage.dat.  (Historically covergroup coverage bypassed --protect-ids and leaked
# these in cleartext.)  The design also self-checks get_inst_coverage(), so sampling
# correctness under hashed names is verified too.
test.compile(verilator_flags2=[
    '--coverage',
    '--protect-ids',
    '--protect-key SECRET_KEY',
    '-Wno-INSECURE',
])

test.execute()

# Security property: no original identifier or source filename in the coverage DB.
test.file_grep_not(test.coverage_filename, r'cgsecret')
test.file_grep_not(test.coverage_filename, r't_covergroup_cross_protect')

# Sanity: 'to="PS"' in the id map means something already-protected was re-protected.
test.file_grep_not(test.obj_dir + "/" + test.vm_prefix + "__idmap.xml", r'to="PS')

test.passes()
