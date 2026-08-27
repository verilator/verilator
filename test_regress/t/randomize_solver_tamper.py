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
# TAMPER: bad_base | bad_digits | bad_index | bad_value | bare_hash | binary
#         | core_junk | crlf | die_at | die_status_at | diversity_model
#         | dup_model | err_assume | err_core | err_multiline | err_once
#         | err_phase | err_reply | err_trunc | err_unbal | err_unbal_cont
#         | garbage_assume | garbage_at | garbage_model | garbage_status
#         | high_digit | indent | low_digit | model_trunc | multiline | mute_at
#         | no_digits | none | octal | oor_assume | phase_model | phase_trunc
#         | short_model | success | unknown_once | unknown_twice | unknown_var
#         | unsat_recheck | unsupported_once | upper_hex
#   bad_base         - replace the Nth model reply with a base character that is not b, o, x or h
#   bad_digits       - replace the Nth model reply with one value holding digits outside its base
#   bad_index        - replace the first array model reply with a bad select index
#   bad_value        - replace the Nth model reply with one well-formed value lacking a base
#   bare_hash        - replace the Nth model reply with one value that is only "#"
#   binary           - replace the Nth model reply with binary values
#   core_junk        - prepend garbage to the core reply and close the pipe
#   crlf             - end every line with CRLF
#   die_at           - kill the solver at the Nth model reply and exit, closing every pipe end
#   die_status_at    - kill the solver at the Nth status line and exit, closing every pipe end
#   diversity_model  - replace the Nth array model reply with one holding an unusable value
#   dup_model        - replace the Nth model reply with one answering a variable twice
#   err_assume       - replace the first unsat-assumptions reply with (error ...)
#   err_core         - replace the first unsat-core reply with (error ...)
#   err_multiline    - answer the Nth status with an (error ...) split over two lines
#   err_once         - answer the Nth status with one (error ...) line
#   err_phase        - replace the first phase value reply with (error ...)
#   err_reply        - replace the Nth S-expression reply with (error ...)
#   err_trunc        - answer the Nth status with an unterminated (error and close the pipe
#   err_unbal        - answer the Nth status with an error closing an extra paren
#   err_unbal_cont   - answer the Nth status with an error, the extra paren on a continuation line
#   garbage_assume   - answer the unsat assumptions with a non-S-expression word
#   garbage_at       - replace every Nth model reply with a non-S-expression line
#   garbage_model    - replace the Nth model reply with a partly valid one
#   garbage_status   - replace the Nth status with a word that is not a status
#   high_digit       - replace the Nth model reply with a digit valid only in a wider base
#   indent           - prepend whitespace to every reply line
#   low_digit        - replace the Nth model reply with a character below any digit or letter
#   model_trunc      - answer the Nth model with an unterminated reply and close the pipe
#   multiline        - split every S-expression reply one token per line
#   mute_at          - close the reply pipe at the Nth model reply but keep this wrapper running
#   no_digits        - replace the Nth model reply with a value whose base has no digits
#   none             - forward every reply unchanged
#   octal            - replace the Nth model reply with octal values
#   oor_assume       - answer the unsat assumptions with an out-of-range literal
#   phase_model      - replace the final phased model reply with (error ...)
#   phase_trunc      - answer an unterminated phase value reply and close the pipe
#   short_model      - replace the Nth model reply with one omitting a requested variable
#   success          - echo a print-success line before every reply
#   unknown_once     - answer the Nth status with unknown
#   unknown_twice    - answer two statuses with unknown
#   unknown_var      - replace the Nth model reply with one naming a variable never requested
#   unsat_recheck    - answer the status that follows an unsat with sat
#   unsupported_once - answer the Nth status with unsupported
#   upper_hex        - replace the Nth model reply with uppercase hex digits
# TAMPER_AT: reply index to act on (default 3)
# TAMPER_ONCE: file marking that the tamper already acted. The runtime restarts
#   a solver that died, which starts this wrapper again, so without the file a
#   mode acts once per solver rather than once per simulation.

# pylint: disable=C0103,C0114,consider-using-with

import os
import re
import shutil
import subprocess
import sys
import time

mode = os.environ.get("TAMPER", "none")
at = int(os.environ.get("TAMPER_AT", "3"))
once = os.environ.get("TAMPER_ONCE", "")

# Modes acting on the TAMPER_AT'th status line rather than the Nth model reply
STATUS_MODES = ("die_status_at", "err_multiline", "err_once", "err_trunc", "err_unbal",
                "err_unbal_cont", "garbage_status", "unknown_once", "unknown_twice",
                "unsupported_once")
# Modes acting on the TAMPER_AT'th S-expression reply of any kind
REPLY_MODES = ("err_reply", )
# Modes acting on an array model reply, which arrives as (select ...) terms
SELECT_MODES = ("bad_index", "diversity_model")
# Modes acting on the status the solver sends after answering unsat
RECHECK_MODES = ("unsat_recheck", )
# phase_model acts on the final phased model; the others on any phase value reply
PHASE_MODES = ("err_phase", "phase_model", "phase_trunc")
# Modes acting on an unsat-assumptions reply, which lists a<N> literals
ASSUME_MODES = ("err_assume", "garbage_assume", "oor_assume")
# Modes acting on an unsat-core reply, which lists cons<N> names
CORE_MODES = ("core_junk", "err_core")
# Modes rewriting every line, so they never consume the index
STREAM_MODES = ("crlf", "indent", "multiline", "success")


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
    elif mode == "indent":
        emit(" \t" + text)
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


def read_full(first):
    """Return the complete S-expression reply that starts at first"""
    chunks = [first]
    left, in_string = scan_depth(first, 0, False)
    while left > 0:
        cont = proc.stdout.readline()
        if not cont:
            break
        chunks.append(cont.rstrip("\n"))
        left, in_string = scan_depth(cont, left, in_string)
    return chunks


def swallow(first):
    """Drop the rest of a real S-expression reply that was replaced"""
    read_full(first)


replies = 0
seen_unsat = False
done = bool(once) and os.path.exists(once)
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
    elif mode in SELECT_MODES:
        counted = at_reply_start and line.startswith("(((select")
    elif mode in RECHECK_MODES:
        counted = is_status and seen_unsat
    elif mode in PHASE_MODES:
        counted = at_reply_start and line.startswith("((x")
    elif mode in ASSUME_MODES:
        counted = at_reply_start and re.match(r"\(a\d", line) is not None
    elif mode in CORE_MODES:
        counted = at_reply_start and line.startswith("(cons")
    else:
        counted = at_reply_start and line.startswith("((")
    if line == "unsat":
        seen_unsat = True
    if counted:
        replies += 1
    acting = counted and replies >= at and not done and mode not in STREAM_MODES
    if not acting:
        forward(line, at_reply_start)
        continue
    if once:
        with open(once, "w", encoding="utf-8"):
            pass

    done = True

    if mode == "bad_base":
        emit("((a #z01) (b #x12))")
        swallow(line)
        continue
    if mode == "bad_digits":
        emit("((a #x0b) (b #xgg))")
        swallow(line)
        continue
    if mode == "bad_index":
        emit("(((select q #xgg) #x15) ((select q #x00000001) #x15)"
             " ((select q #x00000002) #x15))")
        swallow(line)
        continue
    # A well-formed reply whose second value is unusable: the first must not
    # reach the variable either
    if mode == "bad_value":
        emit("((a #x0b) (b bogus))")
        swallow(line)
        continue
    if mode == "bare_hash":
        emit("((a #x0b) (b #))")
        swallow(line)
        continue
    if mode == "binary":
        emit("((a #b00001011) (b #b00010010))")
        swallow(line)
        continue
    if mode == "core_junk":
        emit("junk((cons0))")
        proc.kill()
        proc.wait()
        sys.exit(0)
    # The base model comes first, so a later one belongs to a diversity round
    if mode == "diversity_model":
        emit("(((select q #x00000000) bogus))")
        swallow(line)
        continue
    if mode == "dup_model":
        emit("((a #x0b) (a #x0c) (b #x05))")
        swallow(line)
        continue
    if mode == "err_assume":
        emit('(error "injected assumptions error")')
        swallow(line)
        continue
    if mode == "err_core":
        emit('(error "injected core error")')
        swallow(line)
        continue
    if mode == "err_multiline":
        emit('(error "injected')
        emit('multiline error")')
        continue
    if mode == "err_once":
        emit('(error "injected command rejected")')
        continue
    # The first phase value reply always precedes the final phased model
    if mode == "err_phase":
        emit('(error "injected phase value error")')
        swallow(line)
        continue
    if mode == "err_reply":
        emit('(error "injected reply error")')
        swallow(line)
        continue
    if mode == "err_trunc":
        emit('(error "unterminated')
        proc.kill()
        proc.wait()
        sys.exit(0)
    if mode == "err_unbal":
        emit('(error "unbalanced"))')
        continue
    if mode == "err_unbal_cont":
        emit('(error "unbalanced"')
        emit('))')
        continue
    if mode == "garbage_assume":
        emit("junk")
        swallow(line)
        continue
    # garbage_at repeats, so it re-arms instead of latching
    if mode == "garbage_at":
        replies = 0
        done = False
        emit("junk")
        continue
    if mode == "garbage_model":
        emit("((a #x0b) junk)")
        swallow(line)
        continue
    if mode == "garbage_status":
        emit("flurble")
        continue
    if mode == "high_digit":
        emit("((a #x0b) (b #b2))")
        swallow(line)
        continue
    if mode == "low_digit":
        emit("((a #x0b) (b #x!))")
        swallow(line)
        continue
    if mode == "model_trunc":
        emit("((a #x0b)")
        proc.kill()
        proc.wait()
        sys.exit(0)
    if mode == "no_digits":
        emit("((a #x0b) (b #x))")
        swallow(line)
        continue
    if mode == "octal":
        emit("((a #o13) (b #o12))")
        swallow(line)
        continue
    if mode == "oor_assume":
        emit("(a99999999999999)")
        swallow(line)
        continue
    # Only the final phase queries every variable, so only that reply names y
    if mode == "phase_model":
        replies = 0  # Re-arm until the final phase is seen
        done = False
        parts = read_full(line)
        if "(y " in " ".join(parts):
            emit('(error "injected phased model error")')
        else:
            for part in parts:
                forward(part, part is parts[0])
        continue
    if mode == "phase_trunc":
        emit("((x")
        proc.kill()
        proc.wait()
        sys.exit(0)
    if mode == "short_model":
        emit("((a #x0b))")
        swallow(line)
        continue
    if mode == "unknown_once":
        emit("unknown")
        continue
    if mode == "unknown_twice":
        emit("unknown")
        done = replies >= at + 1
        continue
    if mode == "unknown_var":
        emit("((zzz #x01) (b #x12))")
        swallow(line)
        continue
    # Every re-solve answers the same way, so this re-arms instead of latching
    if mode == "unsat_recheck":
        replies = 0
        seen_unsat = False
        done = False
        emit("sat")
        continue
    if mode == "unsupported_once":
        emit("unsupported")
        continue
    if mode == "upper_hex":
        emit("((a #xAB) (b #x12))")
        swallow(line)
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
