#!/usr/bin/env python3
# mypy: disallow-untyped-defs
# pylint: disable=C0103,C0114,C0116
######################################################################
#
# Snapshot test output directories, and diff them against the snapshot,
# for 'make test-snap' and 'make test-diff'.
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
######################################################################

import argparse
import collections
import concurrent.futures
import filecmp
import fnmatch
import os
import queue
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
from typing import Counter, Iterator, List, Tuple, Union

with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "test_diff_ignore.txt"),
          encoding="utf8") as fh:
    IGNORE_PATTERNS = [line for line in fh.read().splitlines() if line and line[0] != '#']

OBJ_DIRS = ['obj_vlt', 'obj_vltmt', 'obj_dist']

BOLD = "\033[1m"
RED = "\033[31m"
GREEN = "\033[32m"
RESET = "\033[0m"

# Replacements to apply to hide unimportant variance
MASKS = [(re.compile(rb'_h[0-9a-f]{8}_'), b'_hHASH_'),
         (re.compile(rb'0x[0-9a-f]+\*/'), b'0xADDR*/'),
         (re.compile(rb'\brev v[^\s"]*( \(mod\))?'), b'rev REV')]


def masked(path: str) -> bytes:
    with open(path, 'rb') as f:
        data = f.read()
    for regex, replacement in MASKS:
        data = regex.sub(replacement, data)
    return data


def ignored(name: str) -> bool:
    return any(fnmatch.fnmatchcase(name, pat) for pat in IGNORE_PATTERNS)


def walk(top: str) -> Iterator[Tuple[str, List[str], List[str]]]:
    """os.walk, relative to 'top', sorted, and filtered to what the snapshot keeps"""
    for dirpath, dirnames, filenames in os.walk(top):
        # Directory symlinks are not followed by os.walk, so not snapshotted
        dirnames[:] = sorted(d for d in dirnames
                             if not ignored(d) and not os.path.islink(os.path.join(dirpath, d)))
        files = [
            name for name in sorted(filenames)
            if not ignored(name) and not os.access(os.path.join(dirpath, name), os.X_OK)
        ]
        yield os.path.relpath(dirpath, top), dirnames, files


def count_files(path: str) -> int:
    """Number of files the snapshot keeps at 'path', a file or a directory"""
    if not os.path.isdir(path):
        return 1
    return sum(len(files) for _, _, files in walk(path))


def snap(obj_dir: str, snap_obj_dir: str) -> None:
    shutil.rmtree(snap_obj_dir, ignore_errors=True)
    if not os.path.isdir(obj_dir):
        return
    for reldir, _, files in walk(obj_dir):
        os.makedirs(os.path.join(snap_obj_dir, reldir))
        for name in files:
            shutil.copyfile(os.path.join(obj_dir, reldir, name),
                            os.path.join(snap_obj_dir, reldir, name))


def diff_files(a: str, b: str, tool: List[str]) -> str:
    """Diff of the masked contents"""
    with tempfile.TemporaryDirectory() as tmp:
        ta = os.path.join(tmp, 'a')
        tb = os.path.join(tmp, 'b')
        with open(ta, 'wb') as f:
            f.write(masked(a))
        with open(tb, 'wb') as f:
            f.write(masked(b))
        return subprocess.run(tool + ['-L', 'Snapshot: ' + b, '-L', 'Current:  ' + b, ta, tb],
                              stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT,
                              check=False,
                              text=True,
                              errors='replace').stdout


# Output in order: text, or the future of a diff. Printed on its own thread so diffing
# continues while the pager is behind, bounded to limit memory use.
OUTPUT: "queue.Queue[Union[str, concurrent.futures.Future[str], None]]" = queue.Queue(
    maxsize=10000)


def print_output() -> None:
    while (item := OUTPUT.get()) is not None:
        sys.stdout.write(item if isinstance(item, str) else item.result())
        sys.stdout.flush()


def diff(snap_obj_dir: str, obj_dir: str, tool: List[str]) -> Counter[str]:
    """Output differences, and return counts of what was found"""
    stats: Counter[str] = collections.Counter()
    OUTPUT.put(BOLD + "==== " + obj_dir + " ====" + RESET + "\n")
    OUTPUT.put(BOLD + "Snapshot: " + os.path.abspath(snap_obj_dir) + RESET + "\n")
    OUTPUT.put(BOLD + "Current:  " + os.path.abspath(obj_dir) + RESET + "\n")
    # The diff tool can be slow, so run it in parallel
    with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count()) as pool:
        for reldir, dirnames, files in walk(snap_obj_dir):
            obj_dirnames, obj_files = next(walk(os.path.join(obj_dir, reldir)))[1:]
            snap_names = set(dirnames + files)
            obj_names = set(obj_dirnames + obj_files)
            for name in sorted(snap_names | obj_names):
                a = os.path.normpath(os.path.join(snap_obj_dir, reldir, name))
                b = os.path.normpath(os.path.join(obj_dir, reldir, name))
                if name not in obj_names:
                    stats['snapshot'] += count_files(a)
                    OUTPUT.put(RED + "- Only in snapshot: " + b + RESET + "\n")
                elif name not in snap_names:
                    stats['current'] += count_files(b)
                    OUTPUT.put(GREEN + "+ Only in current:  " + b + RESET + "\n")
                elif name in files:
                    stats['compared'] += 1
                    if not filecmp.cmp(a, b, shallow=False) and masked(a) != masked(b):
                        stats['differ'] += 1
                        OUTPUT.put(pool.submit(diff_files, a, b, tool))
            dirnames[:] = [name for name in dirnames if name in obj_dirnames]
    return stats


parser = argparse.ArgumentParser(
    description="Snapshot test output directories, or diff them against the snapshot")
parser.add_argument('command', choices=['snap', 'diff'])
parser.add_argument('--snap-dir', default='snapshot', help='snapshot directory')
Args = parser.parse_args()

# Exit quietly when the pager is quit
if hasattr(signal, 'SIGPIPE'):
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)

pairs = [(os.path.join(Args.snap_dir, obj), obj) for obj in OBJ_DIRS]

if Args.command == 'snap':
    for snap_obj, obj in pairs:
        snap(obj, snap_obj)
    sys.exit(0)

if shutil.which('icdiff'):
    # stdout is usually piped into a pager, so get the width from stderr
    try:
        cols = os.get_terminal_size(sys.stderr.fileno()).columns
    except OSError:
        cols = 80
    Tool = ['icdiff', '-N', '--cols=' + str(cols)]
else:
    Tool = ['diff', '-u', '--color=always']

compare = []
error = False
for snap_obj, obj in pairs:
    if os.path.isdir(snap_obj) and os.path.isdir(obj):
        compare.append((snap_obj, obj))
    elif os.path.isdir(obj):
        print("%Error: No snapshot of " + obj + " in " + os.path.abspath(Args.snap_dir))
        error = True
    elif os.path.isdir(snap_obj):
        print("%Error: Snapshot has " + obj + ", but the current output does not")
        error = True
if error:
    sys.exit(1)

# Daemon, so an error elsewhere cannot leave it blocking exit
printer = threading.Thread(target=print_output, daemon=True)
printer.start()
totals: Counter[str] = collections.Counter()
for snap_obj, obj in compare:
    totals += diff(snap_obj, obj, Tool)
if compare:
    summary = (f"{totals['differ']} of {totals['compared']} files differ,"
               f" {totals['snapshot']} only in snapshot, {totals['current']} only in current")
    OUTPUT.put(BOLD + "==== " + summary + " ====" + RESET + "\n")
    if not totals['differ'] and not totals['snapshot'] and not totals['current']:
        OUTPUT.put(BOLD + "==== All match ====" + RESET + "\n")
OUTPUT.put(None)
printer.join()
