# DESCRIPTION: Verilator: Assertion-control diagnostic output checks
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
"""Compare assertion-control output across independent concurrent processes."""

import re
from pathlib import Path


def normalize_output(text):
    """Keep every report and only order adjacent independent callbacks."""
    lines = []
    pending = []
    seen = set()
    time = None
    for line in text.splitlines(keepends=True):
        stamp = re.match(r'^\[(\d+)\]', line)
        current = stamp[1] if stamp else time
        process = re.search(r'\btop\.t\.concurrent\.[\w.]+', line)
        name = process[0] if process else None
        if not name or current != time or name in seen:
            lines.extend(sorted(pending))
            pending.clear()
            seen.clear()
        if name:
            pending.append(line)
            seen.add(name)
        else:
            lines.append(line)
        time = current
    lines.extend(sorted(pending))
    return ''.join(lines)


def check_output(test, expected):
    """Preserve diagnostic values, counts, time steps and other output order."""
    actual_path = Path(test.obj_dir) / 'concurrent_actual.log'
    expected_path = Path(test.obj_dir) / 'concurrent_expected.log'
    actual_path.write_text(normalize_output(
        Path(test.run_log_filename).read_text(encoding='utf8')),
                           encoding='utf8')
    expected_path.write_text(normalize_output(Path(expected).read_text(encoding='utf8')),
                             encoding='utf8')
    test.files_identical(str(actual_path), str(expected_path), is_logfile=True)
