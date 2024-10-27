#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

root = ".."

Contributors = {'github action': True}
Authors = {}


def read_contributors(filename):
    with open(filename, 'r', encoding="utf8") as fh:
        # Assumes git .mailmap format
        for line in fh:
            line = line.rstrip()
            line = re.sub(r' *<[^>]*>', '', line)
            Contributors[line] = True


def read_user():
    cmd = "cd " + root + " && git diff-index --quiet HEAD --"
    changes = test.run_capture(cmd, check=False)
    changes = changes.rstrip()
    if changes == "":
        if test.verbose:
            print("No git changes")
    else:
        # Uncommitted changes, so check the user's git name
        user = test.run_capture("git config user.name")
        user = user.rstrip()
        if user:
            Authors[user] = True


def read_authors():
    # Check recent commits in case did commit
    cmd = "git log '--pretty=format:%aN <%aE>' | head -5"
    git_auths = test.run_capture(cmd)
    for line in git_auths.splitlines():
        line = re.sub(r' *<[^>]*>', '', line)
        Authors[line] = True


def check():
    read_contributors(root + "/docs/CONTRIBUTORS")
    read_user()
    read_authors()
    for author in sorted(Authors.keys()):
        if test.verbose:
            print("Check: " + author)
        if author not in Contributors:
            test.error("Certify your contribution by sorted-inserting '" + author +
                       "' into docs/CONTRIBUTORS.\n"
                       "   If '" + author +
                       "' is not your real name, please fix 'name=' in ~/.gitconfig\n"
                       "   Also check your https://github.com account's Settings->Profile->Name\n"
                       "   matches your ~/.gitconfig 'name='.\n")


if 'VERILATOR_TEST_NO_CONTRIBUTORS' in os.environ:
    test.skip("Skipping due to VERILATOR_TEST_NO_CONTRIBUTORS")
if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

check()
test.passes()
