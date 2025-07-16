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

root = ".."

if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

test.compile(verilator_flags2=['--assert'],
             nc_flags2=['+assert'],
             vcs_flags2=['-assert svaext'],
             fails=True,
             expect_filename=test.golden_filename)

test.extract(in_filename=test.top_filename,
             out_filename=root + "/docs/gen/ex_USERWARN_faulty.rst",
             regexp=r'\$warn.*User')

test.extract(in_filename=test.top_filename,
             out_filename=root + "/docs/gen/ex_USERERROR_faulty.rst",
             regexp=r'\$error.*User')

test.extract(in_filename=test.top_filename,
             out_filename=root + "/docs/gen/ex_USERINFO_faulty.rst",
             regexp=r'\$info.*User')

test.extract(in_filename=test.top_filename,
             out_filename=root + "/docs/gen/ex_USERFATAL_faulty.rst",
             regexp=r'\$fatal.*User')

test.extract(in_filename=test.golden_filename,
             out_filename=root + "/docs/gen/ex_USERWARN_msg.rst",
             regexp=r'USERWARN:.* User')

test.extract(in_filename=test.golden_filename,
             out_filename=root + "/docs/gen/ex_USERERROR_msg.rst",
             regexp=r'USERERROR:.* User')

test.extract(in_filename=test.golden_filename,
             out_filename=root + "/docs/gen/ex_USERINFO_msg.rst",
             regexp=r'-Info:.* User')

test.extract(in_filename=test.golden_filename,
             out_filename=root + "/docs/gen/ex_USERFATAL_msg.rst",
             regexp=r'USERFATAL:.* User')

test.passes()
