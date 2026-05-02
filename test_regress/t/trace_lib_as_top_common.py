# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import platform
import sys


def run(test, *, verilator_flags2=()):
    fmt, = test.parse_name(r"t_trace_lib_as_top_([a-z]+)")

    if platform.system() == "Windows":
        test.skip("Skipping on Windows: test depends on Unix-style shared-library loading")

    # All test use the same SV file
    test.top_filename = "t/t_trace_lib_as_top.v"
    test.pli_filename = os.path.abspath("t/t_trace_lib_as_top.cpp")
    # Any variations after the format name must yield the exact same trace
    test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"

    flags = [
        f"--trace-{fmt}",
    ]
    flags.extend(verilator_flags2)

    cflags = (f'-DVM_PREFIX={test.vm_prefix} '
              f"-DVM_PREFIX_INCLUDE='<{test.vm_prefix}.h>' ")

    # Compile and run without lib-create
    test.compile(verilator_flags2=[test.pli_filename] + flags +
                 ["--exe", "--build", "-CFLAGS", f'"{cflags}"'])
    test.execute()

    test.trace_identical(test.trace_filename, test.golden_filename)

    # Compile and run with lib-create
    test.compile(verilator_flags2=[test.pli_filename] + flags +
                 ["--build", "--lib-create", "simulator", "-CFLAGS", f'"{cflags}"'])

    # Load library and execute the simulation loop
    # This is to avoid linking manually so that the test is portable
    # Running in test.run() instead of directly to keep output in the test log
    libsim = f"./{test.obj_dir}/libsimulator.so"
    pycode = ("import ctypes;"
              f"lib=ctypes.CDLL({libsim!r});"
              "lib.sim_main(0, None)")
    test.run(cmd=[sys.executable, "-c", f'"{pycode}"'], logfile=test.run_log_filename)

    test.trace_identical(test.trace_filename, test.golden_filename)

    test.passes()
