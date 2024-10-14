#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import datetime

test.scenarios('dist')

RELEASE_OK_RE = r'(^test_regress/t/.*\.(cpp|h|mk|sv|v|vlt)|^test_regress/t_done/|^examples/)'

EXEMPT_AUTHOR_RE = r'(^ci/|^nodist/fastcov.py|^nodist/fuzzer|^test_regress/t/.*\.(cpp|h|v|vlt)$)'

EXEMPT_FILES_RE = r'(^\.|/\.|\.gitignore$|\.dat|\.gprof|\.mem|\.out$|\.png$|\.tree|\.vc$|\.vcd$|^\.)'

EXEMPT_FILES_LIST = """
    Artistic
    CITATION.cff
    CPPLINT.cfg
    LICENSE
    README.rst
    ci/ci-win-compile.ps1
    ci/ci-win-test.ps1
    ci/codecov
    docs/CONTRIBUTING.rst
    docs/CONTRIBUTORS
    docs/README.rst
    docs/_static
    docs/gen
    docs/spelling.txt
    docs/verilated.dox
    include/gtkwave
    include/vltstd
    install-sh
    src/mkinstalldirs
    test_regress/t/t_altera_lpm.v
    test_regress/t/t_flag_f__3.v
    test_regress/t/t_fuzz_eof_bad.v
    test_regress/t/t_incr_void.v
    test_regress/t/t_uvm_pkg_all.vh
    test_regress/t/t_uvm_pkg_todo.vh
    test_regress/t/tsub/t_flag_f_tsub.v
    test_regress/t/tsub/t_flag_f_tsub_inc.v
    verilator.pc.in
    """

root = ".."

Exempt_Files_List_Re = list(map(re.escape, EXEMPT_FILES_LIST.split()))
Exempt_Files_List_Re = '^(' + '|'.join(Exempt_Files_List_Re) + ")"
# pprint(Exempt_Files_List_Re)

if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

cmd = "cd " + root + " && git ls-files --exclude-standard"
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
    open_filename = os.path.join(root, filename)
    if not os.path.exists(open_filename):
        continue
    with open(open_filename, 'r', encoding="utf8") as fh:
        spdx = None
        copyright_msg = None
        release = False
        for line in fh:
            line = line.rstrip()
            if 'SPDX-License-Identifier:' in line:
                spdx = line
            elif re.search(r'Copyright 20[0-9][0-9]', line):
                copyright_msg = line
                if 'Wilson Snyder' in line:
                    pass
                elif re.search(r'\.pl$', filename):
                    pass
                elif re.search(EXEMPT_AUTHOR_RE, filename):
                    pass
                else:
                    if "test_regress/t" in filename:
                        yeardash = str(year)
                    else:
                        yeardash = str(year) + '-' + str(year)
                    print("   " + copyright_msg)
                    test.error_keep_going(filename + ": Please use standard 'Copyright " +
                                          yeardash + " by Wilson Snyder'")
            elif (('Creative Commons Public Domain' in line)
                  or ('freely copied and/or distributed' in line)
                  or ('placed into the Public Domain' in line)):
                release = True

        release_note = ""
        if not re.search(RELEASE_OK_RE, filename):
            release_note = " (has copyright release, but not part of " + RELEASE_OK_RE + ")"
        if not copyright_msg and (not release or release_note):
            test.error_keep_going(filename + ": Please add standard 'Copyright " + str(year) +
                                  " ...', similar to in other files" + release_note)
        if not spdx:
            test.error_keep_going(
                filename +
                ": Please add standard 'SPDX-License_Identifier: ...', similar to in other files")

test.passes()
