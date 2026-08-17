#!/usr/bin/env python3
# DESCRIPTION: Verilator: fake SMT solver wrapper for solver resilience tests
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
# Forwards the SMT-LIB conversation to a real solver, tampering the replies.
#
# Input arguments from environment variables:
# TAMPER: none | die_at | die_status_at | mute_at | garbage_at | err_once
#         | err_multiline | unknown_once | unsupported_once | garbage_status
#         | err_reply | garbage_model | bad_value | bad_digits | short_model
#         | dup_model | success | crlf | multiline
#   die_at           - kill the solver and exit, closing every pipe end
#   die_status_at    - same, counting sat/unsat status lines instead of models
#   mute_at          - close the reply pipe but keep this wrapper running
#   garbage_at       - replace every Nth model reply with a non-S-expression line
#   err_once         - answer the Nth status with one (error ...) line
#   err_multiline    - same, with the error split over two lines
#   unknown_once     - answer the Nth status with unknown
#   unsupported_once - answer the Nth status with unsupported
#   garbage_status   - replace the Nth status with a word that is not a status
#   err_reply        - replace the Nth S-expression reply with (error ...)
#   garbage_model    - replace the Nth model reply with a partly valid one
#   bad_value        - same, but well-formed with one value lacking a base
#   bad_digits       - same, but with one value holding digits outside its base
#   short_model      - same, but omitting a requested variable
#   dup_model        - same, but answering one variable twice
#   success          - echo a print-success line before every reply
#   crlf             - end every line with CRLF
#   multiline        - split every S-expression reply one token per line
# TAMPER_AT: reply index to act on (default 3)

# pylint: disable=C0103,C0114,consider-using-with

import os
import shutil
import subprocess
import sys
import time

mode = os.environ.get("TAMPER", "none")
at = int(os.environ.get("TAMPER_AT", "3"))

# Modes acting on the TAMPER_AT'th status line rather than the Nth model reply
STATUS_MODES = ("die_status_at", "err_once", "err_multiline", "unknown_once", "unsupported_once",
                "garbage_status")
# Modes acting on the TAMPER_AT'th S-expression reply of any kind
REPLY_MODES = ("err_reply", )
# Modes rewriting every line, so they never consume the index
STREAM_MODES = ("success", "crlf", "multiline")


def real_solver():
    """Return argv for the first SMT solver found in PATH"""
    for cmd in (["z3", "-in"], ["cvc5", "--incremental"], ["cvc4", "--lang=smt2",
                                                           "--incremental"]):
        if shutil.which(cmd[0]):
            return cmd
    sys.exit("randomize_solver_tamper.py: no SMT solver found")


proc = subprocess.Popen(real_solver(), stdin=sys.stdin, stdout=subprocess.PIPE, text=True)


def emit(text):
    """Write one reply line downstream, unbuffered"""
    sys.stdout.write(text + ("\r\n" if mode == "crlf" else "\n"))
    sys.stdout.flush()


def forward(text, at_start):
    """Pass a real reply through, applying the whole-stream rewrites"""
    # Solvers echo success per command, so never inside a wrapped S-expression
    if mode == "success" and at_start:
        emit("success")
    if mode == "multiline" and text.startswith("(") and not text.startswith("(error"):
        for tok in text.split():
            emit(tok)
    else:
        emit(text)


def scan_depth(text, left, in_string):
    """Paren depth of text, ignoring parens inside SMT string literals"""
    for char in text:
        if in_string:
            in_string = char != '"'
        elif char == '"':
            in_string = True
        elif char == "(":
            left += 1
        elif char == ")":
            left -= 1
    return left, in_string


def swallow(first):
    """Drop the rest of a real S-expression reply that was replaced"""
    left, in_string = scan_depth(first, 0, False)
    while left > 0:
        cont = proc.stdout.readline()
        if not cont:
            break
        left, in_string = scan_depth(cont, left, in_string)


replies = 0
done = False
depth = 0  # Paren depth of the reply being forwarded, so wrapped ones stay intact
inside = False  # Inside an SMT string literal, where parens do not nest

for line in proc.stdout:
    line = line.rstrip("\n")
    at_reply_start = depth == 0
    depth, inside = scan_depth(line, depth, inside)
    is_status = line in ("sat", "unsat", "unknown")
    if mode in STATUS_MODES:
        counted = is_status
    elif mode in REPLY_MODES:
        # Only a first line opens a reply; a wrapped continuation is not a new one
        counted = at_reply_start and line.startswith("(")
    else:
        counted = at_reply_start and line.startswith("((")
    if counted:
        replies += 1
    acting = counted and replies >= at and not done and mode not in STREAM_MODES
    if not acting:
        forward(line, at_reply_start)
        continue

    # garbage_at repeats, so it re-arms instead of latching
    if mode == "garbage_at":
        replies = 0
        emit("junk")
        continue
    done = True

    if mode == "garbage_status":
        emit("flurble")
        continue
    if mode == "unknown_once":
        emit("unknown")
        continue
    if mode == "err_reply":
        emit('(error "injected reply error")')
        swallow(line)
        continue
    if mode == "garbage_model":
        emit("((a #x0b) junk)")
        swallow(line)
        continue
    # A well-formed reply whose second value is unusable: the first must not
    # reach the variable either
    if mode == "bad_value":
        emit("((a #x0b) (b bogus))")
        swallow(line)
        continue
    if mode == "bad_digits":
        emit("((a #x0b) (b #xgg))")
        swallow(line)
        continue
    if mode == "short_model":
        emit("((a #x0b))")
        swallow(line)
        continue
    if mode == "dup_model":
        emit("((a #x0b) (a #x0c) (b #x05))")
        swallow(line)
        continue

    # These replace the awaited status, which is how a real solver answers a
    # command it rejected: no status follows, so nothing is forwarded
    if mode == "err_once":
        emit('(error "injected command rejected")')
        continue
    if mode == "err_multiline":
        emit('(error "injected')
        emit('multiline error")')
        continue
    if mode == "unsupported_once":
        emit("unsupported")
        continue
    forward(line, at_reply_start)

    if mode in ("die_at", "die_status_at"):
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
