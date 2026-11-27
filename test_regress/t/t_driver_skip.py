#!/usr/bin/env python3
# DESCRIPTION: Verilator: Preserve comparison failures before a later skip
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import pickle
import subprocess
import sys
from pathlib import Path

import vltest_bootstrap

test.scenarios('dist')

driver = str(Path('driver.py').resolve())
directory = Path(test.obj_dir).resolve() / 'child'
test_dir = directory / 't'
test_dir.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
env.pop('HARNESS_UPDATE_GOLDEN', None)
env.pop('TEST_REGRESS', None)
env.pop('VERILATOR_TESTS_SITE', None)
for mismatch in (False, True):
    for skip in (False, True):
        name = 't_child_' + str(int(mismatch)) + str(int(skip))
        source = """import vltest_bootstrap
test.scenarios('dist')
test.write_wholefile(test.obj_dir + '/actual.txt', 'actual\\n')
test.write_wholefile(test.obj_dir + '/expected.txt', %r)
test.files_identical(test.obj_dir + '/actual.txt', test.obj_dir + '/expected.txt')
%s
test.passes()
""" % ('different\n' if mismatch else 'actual\n',
        "test.skip('Optional tool unavailable')" if skip else '')
        (test_dir / (name + '.py')).write_text(source, encoding="utf8")
        result = subprocess.run(
            [sys.executable, driver, '--dist', '--jobs', '1', 't/' + name + '.py'],
            cwd=directory,
            env=env,
            capture_output=True,
            text=True,
            check=False,
            timeout=30)
        (directory / (name + '.log')).write_text(result.stdout + result.stderr, encoding="utf8")
        status = directory / 'obj_dist' / name / ('V' + name + '.status')
        with status.open('rb') as stream:
            outcome = pickle.load(stream)
        if result.returncode != (10 if mismatch else 0):
            test.error(name + ': Unexpected driver exit status ' + str(result.returncode))
        assert bool(outcome['errors']) == mismatch, outcome
        assert bool(outcome['_skips']) == skip, outcome
        assert bool(outcome['_ok']) == (not mismatch and not skip), outcome

test.passes()
