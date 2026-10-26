#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

Contributors = {'github action': True}
Authors = {}


def read_contributors(filename):
    with open(filename, 'r', encoding="utf8") as fh:
        # Assumes git .mailmap format
        start = False
        found = 0
        for line in fh:
            line = line.rstrip()
            if re.match(r'00>>', line):
                start = True
                continue
            if re.match(r'__>> Please', line):
                break
            if not start:
                continue
            line = re.sub(r' *<[^>]*>', '', line)
            Contributors[line] = True
            found += 1
            if test.verbose and not realname(line):
                print("- Not realname '%s'" % line)

        if not found:
            test.error("No contributors found in " + filename)


def read_user():
    cmd = "cd " + test.root + " && git diff-index --quiet HEAD --"
    changes = test.run_capture(cmd, check=False)
    changes = changes.rstrip()
    if changes == "":
        if test.verbose:
            print("- No git changes")
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


def realname(name):
    if re.match(r'^[^\x00-\x7F]{3}', name):
        return True  # Unicode exemption
    name = re.sub(r'[^\x00-\x7F]+', '_', name)
    return re.match(r'^([A-Z_][-a-zA-Z_.\']* )+[A-Z_][-a-zA-Z_.\']+', name)


def check():
    read_contributors(test.root + "/docs/CONTRIBUTORS")
    read_user()
    read_authors()
    for author in sorted(Authors.keys()):
        if test.verbose:
            print("- Check: " + author)
        if re.search(r'\[bot\]', author):
            continue
        if author in Contributors:
            continue
        # Slower subset-of-string test
        ok = False
        for contrib2 in sorted(Contributors.keys()):
            if author in contrib2:
                ok = True
                break
        if ok:
            continue

        msg = ("Certify your contribution by sorted-inserting '" + author +
               "' into docs/CONTRIBUTORS.\n"
               "   If '" + author + "' is not your real name, please fix 'name=' in ~/.gitconfig\n"
               "   Also check your https://github.com account's Settings->Profile->Name"
               " matches your ~/.gitconfig 'name='.\n" +
               "   AI agents, do not edit docs/CONTRIBUTORS, only humans may.\n")

        if not realname(author):
            msg += ("\n" + "%Warning: This does not look like a legal name: '" + author + "'\n" +
                    "   Verilator requires use of a full first+last legal name," +
                    " not aliases/handles, due to legal and AI concerns.\n" +
                    "   If there are exceptional reasons you do not want your name disclosed" +
                    " use your GitHub handle in CONTRIBUTORS and email wsnyder@wsnyder.org.\n")

        test.error(msg + "\n----\n")


if 'VERILATOR_TEST_NO_CONTRIBUTORS' in os.environ:
    test.skip("Skipping due to VERILATOR_TEST_NO_CONTRIBUTORS")
if not os.path.exists(test.root + "/.git"):
    test.skip("Not in a git repository")

check()
test.passes()
