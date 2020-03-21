#!/bin/bash
######################################################################
# DESCRIPTION: Fuzzer run script
#
# Copyright 2019-2019 by Eric Rippey. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
######################################################################

# Actually do the fuzzing.  Note that this will not terminate in any reasonable
# amount of time.  However, it will give updates on its progress.
afl-fuzz -i in1 -o out1 -x dictionary ./wrapper --cc @@
