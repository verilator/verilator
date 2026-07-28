#!/usr/bin/env python3
# DESCRIPTION: Verilator: fake SMT solver wrapper for solver resilience tests
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
# Forwards the SMT-LIB conversation to a real solver and tampers the reply stream.
# Response index = 1-based count of sat/unsat/unknown lines (1 = init handshake).
#
# Input arguments from environment variables:
# TAMPER: none | err_once | err_multiline | unknown_once | unsupported_once
#         | die_at | epipe_at | silent_at | garbage_status | garbage_model | crlf
#         | success | multiline | stall_stdin | err_reply | garbage_reply
# TAMPER_AT: response index for the one-shot modes above (default 2);
#            err_reply and garbage_reply count paren replies instead of statuses

# pylint: disable=C0114,consider-using-with

import os
import shutil
import subprocess
import sys
import threading

mode = os.environ.get("TAMPER", "none")
at = int(os.environ.get("TAMPER_AT", "2"))


def real_solver():
    """Return argv for the first SMT solver found in PATH"""
    for cmd in (["z3", "-in"], ["cvc5", "--incremental"], ["cvc4", "--lang=smt2",
                                                           "--incremental"]):
        if shutil.which(cmd[0]):
            return cmd
    sys.exit("randomize_solver_tamper.py: no SMT solver found")


stall = threading.Event()

if mode == "stall_stdin":
    # Interpose stdin so the pump can stop consuming, backpressuring the model
    proc = subprocess.Popen(real_solver(),
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            text=True)

    def pump():
        """Forward stdin to the solver until the stall event fires"""
        while not stall.is_set():
            data = sys.stdin.buffer.read1(4096)
            if not data:
                proc.stdin.close()
                return
            proc.stdin.write(data.decode())
            proc.stdin.flush()

    threading.Thread(target=pump, daemon=True).start()
else:
    proc = subprocess.Popen(real_solver(), stdin=sys.stdin, stdout=subprocess.PIPE, text=True)

n = 0
replies = 0
done = False


def emit(text, ending="\n"):
    """Write one reply line downstream, unbuffered"""
    sys.stdout.write(text + ending)
    sys.stdout.flush()


def swallow(first):
    """Consume the rest of the real reply until its parens balance"""
    depth = first.count("(") - first.count(")")
    while depth > 0:
        cont = proc.stdout.readline()
        if not cont:
            break
        depth += cont.count("(") - cont.count(")")


for line in proc.stdout:
    line = line.rstrip("\n")
    is_status = line in ("sat", "unsat", "unknown")
    if line.startswith("("):
        replies += 1
        if not done and replies >= at:
            if mode == "err_reply":
                emit('(error "injected reply error")')
                done = True
                swallow(line)
                continue
            if mode == "garbage_reply":
                emit("junk")
                done = True
    if is_status:
        n += 1
        if not done and n >= at:
            if mode == "err_once":
                emit('(error "injected transient desync")')
                done = True
            elif mode == "err_multiline":
                emit('(error "injected')
                emit('multiline error")')
                done = True
            elif mode == "unknown_once":
                emit("unknown")
                done = True
                continue
            elif mode == "unsupported_once":
                emit("unsupported")
                done = True
            elif mode == "die_at":
                proc.kill()
                proc.wait()
                sys.exit(0)
            elif mode == "epipe_at":
                os.close(0)
                proc.kill()
                proc.wait()
                emit(line)
                sys.exit(0)
            elif mode == "silent_at":
                emit('(error "injected silence")')
                done = True
                continue
            elif mode == "garbage_status":
                emit("flurble")
                done = True
                continue
            elif mode == "stall_stdin":
                stall.set()
                done = True
    elif mode == "garbage_model" and not done and n >= at and line.startswith("(("):
        emit('((a #x0b) junk)')
        done = True
        swallow(line)
        continue
    if mode == "crlf":
        emit(line, "\r\n")
    elif mode == "success":
        emit("success")
        emit(line)
    elif mode == "multiline" and line.startswith("(") and not line.startswith("(error"):
        for tok in line.split():
            emit(tok)
    else:
        emit(line)
