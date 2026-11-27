#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verify bundled partitioner source provenance
# SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import hashlib
import json
import os
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
    original_hashes = {}
    for package in packages:
        for filename, expected in package['files'].items():
            relative = Path('third_party') / package['path'] / filename
            original_hashes[relative] = expected
            original = root / relative
            actual = hashlib.sha256(original.read_bytes()).hexdigest()
            if actual != expected:
                target = staging / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(original, target)
                changed[target] = expected
    # Embedding patches may add files absent from the upstream manifest.
    # Include them so reverse application also verifies their full contents.
    added = set()
    for patch in sorted((bundled / 'patches').glob('*.patch')):
        records = subprocess.check_output(
            ['git', 'apply', '--numstat', '-z', str(patch)], cwd=root)
        for record in records.decode().split('\0'):
            if not record:
                continue
            relative = Path(record.split('\t', 2)[2])
            assert relative.parts[0] == 'third_party' and '..' not in relative.parts
            original = root / relative
            target = staging / relative
            if original.is_file() and not target.exists():
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(original, target)
                if relative in original_hashes:
                    changed[target] = original_hashes[relative]
                else:
                    added.add(target)
    # Imported code is exempt from Verilator's style checks. Every difference
    # must instead be explained by the reviewed embedding patches.
    for patch in reversed(sorted((bundled / 'patches').glob('*.patch'))):
        # Apply relative to the staging tree, without inheriting the enclosing
        # checkout's path prefix for git-format patches.
        subprocess.run(['git', 'apply', '--reverse', str(patch)],
                       cwd=staging,
                       env=dict(os.environ, GIT_CEILING_DIRECTORIES=str(staging.parent)),
                       check=True)
    for filename in added:
        assert not filename.exists(), filename
    for filename, expected in changed.items():
        assert hashlib.sha256(filename.read_bytes()).hexdigest() == expected, filename

test.passes()
