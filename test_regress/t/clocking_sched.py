# DESCRIPTION: Verilator: Clocking scheduler output checks
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
"""Compare clocking scheduler traces while allowing independent callbacks."""

import re
from pathlib import Path


def normalize_output(output):
    """Order independent notifications without crossing scheduler iterations."""
    # Independent processes in the same event region may execute in any order
    # (IEEE 1800-2023 4.7). Only group adjacent clocking-input callbacks, or the
    # initial zero-value notifications. Keep posedges, NBA transitions, output
    # drives and postponed observations as boundaries, even at the same time.
    callbacks = {'cb.a': 0, 'cb.b': 1, 'cb.y': 2, 'b': 3}
    initial = {'z<=0': 0, 'x<=0': 1, 'y=0': 2, 'c<=0': 3}
    result = []
    pending = []
    group = None
    seen = set()
    for line in output.splitlines(keepends=True):
        match = re.fullmatch(r'\[(\d+)\] (.*)\n', line)
        key = None
        rank = None
        if match:
            stamp, message = match.groups()
            label = message.split('=', 1)[0]
            if label in callbacks:
                key, rank = (stamp, 'callback'), callbacks[label]
            elif stamp == '0' and message in initial:
                key, rank = (stamp, 'initial'), initial[message]
        # A repeated label is a new notification, not another independent
        # process. Never sort two observations from the same process together.
        if key != group or rank in seen:
            result.extend(text for _, text in sorted(pending))
            pending.clear()
            seen.clear()
            group = key
        if key is None:
            result.append(line)
        else:
            pending.append((rank, line))
            seen.add(rank)
    result.extend(text for _, text in sorted(pending))
    return ''.join(result)


def check_output(test):
    """Compare the complete trace after ordering only independent callbacks."""
    logfile = Path(test.obj_dir) / 'vlt_sim.log'
    normalized = logfile.with_suffix('.normalized.log')
    normalized.write_text(normalize_output(logfile.read_text(encoding='utf8')), encoding='utf8')
    test.files_identical(str(normalized), test.golden_filename, is_logfile=True)
