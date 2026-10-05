#!/usr/bin/env python3
# DESCRIPTION: Verilator: Duplicate packages in different libraries
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('linter')

test.lint(top_filename='t/t_package_dup_lib_bad.v',
          v_other_filenames=['t/t_package_dup_lib_bad_other.v'],
          verilator_flags2=['-libmap t/t_package_dup_lib_bad.map'],
          fails=True,
          expect_filename=test.golden_filename)

test.passes()
