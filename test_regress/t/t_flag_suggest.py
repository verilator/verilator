#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

opts = []
# Typo
opts += ["-ccc"]
# Typo of an option that starts with "--"
opts += ["--ccc"]
# Typo of an option that starts with "-no-"
opts += ["-no-asserT"]
# Typo of an option that starts with "-no"
opts += ["-noasserT"]
# Typo of an option that allows "-no"
opts += ["-asserT"]
# Typo of an option that starts with '+'
opts += ["+definE+A=B"]
# Typo that takes arg
opts += ["-CFLAGs -ggdb"]
# Typo of an undocumented option
opts += ["-debug-aborT"]
# Typo of "-Wno" for partial match
opts += ["-Won-SPLITVAR"]
# Typo after -Wno- for partial match
opts += ["-Wno-SPLITVER"]
# Typo of -language
opts += ["-language 1364-1997"]

cmd = ""
for var in opts:
    cmd += os.environ["VERILATOR_ROOT"] + "/bin/verilator " + var + "; "

test.run(cmd=[cmd],
         verilator_run=True,
         logfile=test.obj_dir + "/sim.log",
         fails=True,
         expect_filename=test.golden_filename)

test.passes()
