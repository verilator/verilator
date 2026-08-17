#!/usr/bin/env python3

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=["--public-flat-rw -CFLAGS -Werror"])

test.passes()