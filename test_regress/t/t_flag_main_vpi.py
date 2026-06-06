#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# Compile with --binary --vpi to exercise the VPI-aware generated main.
# Also compile a VPI shared library to be loaded at runtime via +verilator+vpi+.
test.compile(
    make_pli=True,
    verilator_flags2=["--binary --vpi --public-flat-rw"])

# With --vpi and an executable (--binary implies --exe), the Makefile must, on Linux,
# export the executable's symbols (-rdynamic) and link libdl for the generated loader's
# dlopen/dlsym calls.  These are gated on $(UNAME_S) so macOS/Windows are unaffected.
mk = test.obj_dir + "/V" + test.name + ".mk"
test.file_grep(mk, r'ifeq \(\$\(UNAME_S\),Linux\)')
test.file_grep(mk, r'LDFLAGS \+= -rdynamic')
test.file_grep(mk, r'LDLIBS \+= -ldl')

# Run the generated binary; load the VPI library via the +verilator+vpi+ plusarg.
test.execute(all_run_flags=["+verilator+vpi+" + test.obj_dir + "/libvpi.so"],
             check_finished=True)

test.passes()
