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

Tabs_Exempt_Re = r'(\.out$)|(/gtkwave)|(Makefile)|(\.mk$)|(\.mk\.in$)|test_regress/t/t_preproc\.v|install-sh'


def get_source_files(root):
    git_files = test.run_capture("cd " + root + " && git ls-files")
    if test.verbose:
        print("MF " + git_files)
    files = {}
    for filename in git_files.split():
        if filename == '':
            continue
        files[filename] = True
    return files


if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

root = ".."

files = get_source_files(root)

warns = {}
fcount = 0
for filename in sorted(files.keys()):
    filename = os.path.join(root, filename)
    if not os.path.exists(filename):  # git file might be deleted but not yet staged
        continue
    contents = test.file_contents(filename)
    if re.search(r'(\.out|\.dat)$', filename):
        continue  # Ignore golden files
    if re.search(r'[\001\002\003\004\005\006]', contents):
        continue  # Ignore binary files
    if contents != "" and contents[-1] != "\n":
        contents += "\n"
        warns[filename] = "Missing trailing newline (add one) in " + filename
    if "\r" in contents:
        contents = re.sub(r'\r', '', contents)
        warns[filename] = "Carriage returns (remove them) in: " + filename
    if "\f" in contents:
        contents = re.sub(r'\f', '', contents)
        warns[filename] = "Form-feeds (remove them) in: " + filename
    if "\t" in contents and not re.search(Tabs_Exempt_Re, filename):
        warns[filename] = "Tabs (cannot --gold fix) in " + filename

    if (re.search(r'[ \t]\n', contents)
            or re.search(r'\n\n+$', contents)):  # Regexp repeated below
        eol_ws_exempt = ('spelling.txt' in filename or '/gtkwave/' in filename)
        if eol_ws_exempt:
            continue
        if 'HARNESS_UPDATE_GOLDEN' in os.environ:
            changes = False
            (contents, n) = re.subn(r'[ \t]+\n', '\n', contents)
            if n:
                changes = True
            if not eol_ws_exempt:
                (contents, n) = re.subn(r'\n\n+$', '\n', contents)
                if n:
                    changes = True
            if not changes:
                continue
            warns[filename] = "Updated whitespace at " + filename
            test.write_wholefile(filename, contents)
            continue

        lineno = 0
        for line in contents.splitlines():
            lineno += 1
            if re.search(r'\s$', line):
                warns[filename] = "Trailing whitespace at " + filename + ":" + str(lineno)
                warns[filename] += " (last character is ASCII " + str(ord(line[-1])) + ")"

        if not eol_ws_exempt and re.search(r'\n\n+$', contents):  # Regexp repeated above
            warns[filename] = "Trailing newlines at EOF in " + filename

    # Unicode checker; should this be done in another file?
    # No way to auto-fix.
    unicode_exempt = (re.search(r'Changes$', filename) or re.search(r'CONTRIBUTORS$', filename)
                      or re.search(r'contributors.rst$', filename)
                      or re.search(r'spelling.txt$', filename))
    if not unicode_exempt and re.search(r'[^ \t\r\n\x20-\x7e]', contents):
        warns[filename] = "Warning: non-ASCII contents in " + filename

    fcount += 1

if fcount < 50:
    test.error("Too few source files found")

if len(warns):
    # First warning lists everything as that's shown in the driver summary
    msg = ""
    if 'HARNESS_UPDATE_GOLDEN' in os.environ:
        msg += "Updated files with whitespace errors: " + ' '.join(sorted(warns.keys())) + "\n"
    else:
        msg += "Files have whitespace errors: " + ' '.join(sorted(warns.keys())) + "\n"
        msg += "To auto-fix: HARNESS_UPDATE_GOLDEN=1 {command} or --golden\n"
    for filename in sorted(warns.keys()):
        msg += warns[filename] + "\n"
    test.error(msg)

test.passes()
