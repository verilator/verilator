#!/usr/bin/env python3
# DESCRIPTION: Verilator: fake SMT solver wrapper for solver resilience tests
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
# Forwards the SMT-LIB conversation to a real solver, then kills it.
#
# Input arguments from environment variables:
# TAMPER: none | die_at | mute_at
#   die_at  - kill the solver and exit, closing every pipe end
#   mute_at - close the reply pipe but keep this wrapper running
# TAMPER_AT: model reply index to die on (default 3)

# pylint: disable=C0103,C0114,consider-using-with

import os
import shutil
import subprocess
import sys
import time

mode = os.environ.get("TAMPER", "none")
at = int(os.environ.get("TAMPER_AT", "3"))


def real_solver():
    """Return argv for the first SMT solver found in PATH"""
    for cmd in (["z3", "-in"], ["cvc5", "--incremental"], ["cvc4", "--lang=smt2",
                                                           "--incremental"]):
        if shutil.which(cmd[0]):
            return cmd
    sys.exit("randomize_solver_tamper.py: no SMT solver found")


proc = subprocess.Popen(real_solver(), stdin=sys.stdin, stdout=subprocess.PIPE, text=True)

replies = 0

for line in proc.stdout:
    line = line.rstrip("\n")
    if line.startswith("(("):
        replies += 1
    sys.stdout.write(line + "\n")
    sys.stdout.flush()
    if replies < at:
        continue
    if mode == "die_at":
        proc.kill()
        proc.wait()
        sys.exit(0)
    if mode == "mute_at":
        os.close(1)
        proc.kill()
        proc.wait()
        parent = os.getppid()
        while os.getppid() == parent:
            time.sleep(0.05)
        sys.exit(0)
