#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verify bundled partitioner source provenance
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import hashlib
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

import vltest_bootstrap

test.scenarios('dist')
root = Path(test.root).resolve()
bundled = root / 'third_party'
packages = json.loads((bundled / 'manifest.json').read_text(encoding='utf8'))
with tempfile.TemporaryDirectory(dir=test.obj_dir) as directory:
    staging = Path(directory).resolve()
    changed = {}
    for package in packages:
        for filename, expected in package['files'].items():
            relative = Path('third_party') / package['path'] / filename
            original = root / relative
            actual = hashlib.sha256(original.read_bytes()).hexdigest()
            if actual != expected:
                target = staging / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(original, target)
                changed[target] = expected
    # Imported code is exempt from Verilator's style checks. Every difference
    # must instead be explained by the reviewed embedding patches.
    for patch in reversed(sorted((bundled / 'patches').glob('*.patch'))):
        subprocess.run(['git', 'apply', '--reverse', str(patch)], cwd=staging, check=True)
    for filename, expected in changed.items():
        assert hashlib.sha256(filename.read_bytes()).hexdigest() == expected, filename

test.passes()
