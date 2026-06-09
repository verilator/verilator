#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test for dpi unpack array
#
# author: Yilin Li

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=["--binary"])

test.execute()

test.passes()
