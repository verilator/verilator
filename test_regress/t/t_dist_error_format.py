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

# Check all error messages match our standard format
# This assumes .out files cover all important errors


def formats():
    files = root + "/test_regress/t/*.out"
    warns = {}
    lnmatch = 0
    for filename in test.glob_some(files):
        wholefile = test.file_contents(filename)
        filename = os.path.basename(filename)
        if re.search(r'(Exiting due to|%Error|%Warning)', wholefile):
            lineno = 0
            for line in wholefile.splitlines():
                lineno += 1
                line = re.sub(r'(\$display|\$write).*\".*%(Error|Warning)', '', line)
                line = re.sub(r'<---.*', '', line)
                if (re.search(r'(Error|Warning)', line)
                        and not re.search(r'^\s*<sformatf ', line)  # skip XML tag
                        and not re.search(r'^\s*{"type":"', line)  # skip JSON node
                        and not re.search(r'Error-internal-contents-bad', line)):
                    # These formats are documented in bin/verilator
                    # Error with fileline
                    # For testing only: we assume no : in filename
                    match = line
                    match = re.sub(r'^\[\d+\] ', '', match)  # Simplify runtime errors
                    if re.search(r'^%(Error|Warning)(-[A-Z0-9_]+)?: ([^:]+):(\d+):((\d+):)? ',
                                 match):
                        lnmatch += 1
                        if test.verbose:
                            print("ok-el " + filename + " " + line)
                    # Error no fileline
                    # For testing only: we assume any : is single quoted
                    elif re.search(r"^%(Error|Warning)(-[A-Z0-9_]+)?: [^:']+", match):
                        if test.verbose:
                            print("ok-en " + filename + " " + line)
                    else:
                        #print("FF "+filename+": "+line)
                        fline = filename + ":" + str(lineno)
                        warns[fline] = "Non-standard warning/error: " + fline + ": " + line
                        if test.verbose:
                            print(warns[fline])

    if not lnmatch:
        test.error("Check line number regexp is correct, no matches")
    if len(warns):
        # First warning lists everything as that's shown in the driver summary
        test.error_keep_going(' '.join(sorted(warns.keys())))
        for filename in sorted(warns.keys()):
            test.error_keep_going(warns[filename])


if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

formats()

test.passes()
