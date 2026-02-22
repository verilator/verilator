#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import datetime

test.scenarios('dist')

RELEASE_OK_RE = r'(^test_regress/t/.*\.(cpp|h|map|mk|sv|v|vlt)|^test_regress/t_done/|^examples/)'

EXEMPT_AUTHOR_RE = r'(^ci/|^nodist/fastcov.py|^nodist/fuzzer|^test_regress/t/.*\.(cpp|h|mk|s?vh?|vlt)$)'

EXEMPT_FILES_RE = r'(^\.|/\.|\.gitignore$|\.dat|\.gprof|\.mem|\.out$|\.png$|\.tree|\.vc$|\.vcd$|^\.)'

EXEMPT_FILES_LIST = """
    CITATION.cff
    CPPLINT.cfg
    LICENSE
    LICENSES/
    REUSE.toml
    ci/ci-win-compile.ps1
    ci/ci-win-test.ps1
    ci/codecov
    docs/CONTRIBUTORS
    docs/_static
    docs/gen
    docs/spelling.txt
    docs/verilated.dox
    include/gtkwave
    include/vltstd
    install-sh
    src/mkinstalldirs
    test_regress/t/t_altera_lpm.v
    test_regress/t/t_randsequence_svtests.v
    test_regress/t/uvm/
    verilator.pc.in
    """

Exempt_Files_List_Re = list(map(re.escape, EXEMPT_FILES_LIST.split()))
Exempt_Files_List_Re = '^(' + '|'.join(Exempt_Files_List_Re) + ")"
# pprint(Exempt_Files_List_Re)

if not os.path.exists(test.root + "/.git"):
    test.skip("Not in a git repository")

cmd = "cd " + test.root + " && git ls-files --exclude-standard"
out = test.run_capture(cmd)

year = datetime.datetime.now().year

files = {}
out = re.sub(r'\s+', ' ', out)
for filename in out.split():
    if re.search(EXEMPT_FILES_RE, filename):
        continue
    if re.search(Exempt_Files_List_Re, filename):
        continue
    files[filename] = True

for filename in files:
    open_filename = os.path.join(test.root, filename)
    if not os.path.exists(open_filename):
        continue

    if "test_regress/t" in filename:
        yeardash = str(year)
    else:
        yeardash = str(year) + '-' + str(year)

    with open(open_filename, 'r', encoding="utf8") as fh:
        spdx = None
        copyright_msg = None
        for line in fh:
            line = line.rstrip()
            if 'SP' + 'DX-License-Identifier:' in line:
                spdx = line
            elif re.search(r'(SP()DX-FileCopyrightText: 20[0-9][0-9])', line):
                copyright_msg = line
                if 'Wilson Snyder' in line:
                    pass
                elif re.search(EXEMPT_AUTHOR_RE, filename):
                    pass
                else:
                    print("   " + copyright_msg)
                    test.error_keep_going(filename + ": Please use standard 'SP" +
                                          "DX-FileCopyrightText: " + yeardash + " Wilson Snyder'")

        if not copyright_msg:
            test.error_keep_going(filename + ": Please add standard 'SP" +
                                  "DX-FileCopyrightText: " + yeardash +
                                  " ...', similar to in other files")
        if not spdx:
            test.error_keep_going(filename + ": Please add standard 'SP" +
                                  "DX-License-Identifier: ...', similar to in other files")

test.passes()
