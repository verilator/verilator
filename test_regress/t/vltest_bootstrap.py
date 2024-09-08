# DESCRIPTION: Verilator: Verilog Test bootstrap loader
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import re
import sys

os.chdir(os.path.dirname(os.path.realpath(__file__)) + "/..")
# Avoid chdir leaving the .. which confuses later commands
os.environ['PWD'] = os.getcwd()
args = list(map(lambda arg: re.sub(r'.*/test_regress/', '', arg), sys.argv))
os.execl("./driver.py", "--bootstrapped", *args)
