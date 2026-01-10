#!/usr/bin/env python3
# DESCRIPTION: Verilator: Primitive C++ style checker
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

Doc_Waivers = [
    '+verilator+prof+threads+file+',  # Deprecated
    '+verilator+prof+threads+start+',  # Deprecated
    '+verilator+prof+threads+window+',  # Deprecated
    '-clk',  # Deprecated
    '-lineno',  # Deprecated
    '-order-clock-delay',  # Deprecated
    '-pp-comments',  # Deprecated
    '-prof-threads',  # Deprecated
    '-xml-only',  # Removed
    '-xml-output',  # Removed
]

Test_Waivers = [
    # Covered:
    '-G',  # Covered; other text fallows option letter
    '-O',  # Covered; other text fallows option letter
    '-U',  # Covered; other text fallows option letter
    '-gdb',  # Covered: no way to test, part of --gdbbt
    '-rr',  # Not testing; not requiring rr installation
    # Need testing:
    '-fconst',  # TODO breaks due to some needed V3Const steps
]

Sums = {}
Docs = {}
Srcs = {}
Tests = {}


def read_sums():
    for filename in test.glob_some(test.root + "/bin/*"):
        with open(filename, "r", encoding="latin-1") as fh:
            on = False
            lineno = 0
            for line in fh:
                lineno += 1
                line = line.rstrip()
                m1 = re.search(r'^\s+((-|\+)+[^ ]+)', line)
                m2 = re.search(r"parser.add_argument\('((-|\+)[^']+)'", line)
                if re.search(r'ARGUMENT SUMMARY', line):
                    on = True
                elif re.search(r'=head1', line):
                    on = False
                elif on and m1:
                    opt = opt_clean(m1.group(1))
                    key = opt_key(opt)
                    if test.verbose:
                        print("A '" + opt + "' " + line)
                    Sums[key] = filename + ":" + str(lineno) + ": " + opt
                elif m2:
                    opt = opt_clean(m2.group(1))
                    key = opt_key(opt)
                    if test.verbose:
                        print("A '" + opt + "' " + line)
                    Sums[key] = filename + ":" + str(lineno) + ": " + opt


def read_docs():
    for filename in test.glob_some(test.root + "/docs/guide/*.rst"):
        with open(filename, "r", encoding="latin-1") as fh:
            lineno = 0
            for line in fh:
                lineno += 1
                line = line.rstrip()
                m = re.search(r'option:: ((-|\+)+[^ `]+)', line)
                if not m:
                    m = re.search(r':vlopt:`[^`]+ <([^>]+)>', line)
                if not m:
                    m = re.search(r':vlopt:`((-|\+)+[^ `]+)', line)
                if m:
                    opt = opt_clean(m.group(1))
                    key = opt_key(opt)
                    if test.verbose:
                        print("D '" + opt + "' " + line)
                    Docs[key] = filename + ":" + str(lineno) + ": " + opt


def read_srcs():
    filename = "bin/verilator --debug-options"
    opts = test.run_capture("perl " + os.environ["VERILATOR_ROOT"] + "/bin/verilator" +
                            " --debug-options 2>&1")
    lineno = 0
    for line in opts.split("\n"):
        lineno += 1
        m1 = re.search(r'OPTION: "([^"]+)"', line)
        if m1:
            opt = opt_clean(m1.group(1))
            key = opt_key(opt)
            if re.match(r'-Werror-[A-Z ]', opt):
                continue
            if re.match(r'-Wno-[A-Z ]', opt):
                continue
            if re.match(r'-Wwarn-[A-Z ]', opt):
                continue
            if test.verbose:
                print("S '" + opt + "' " + line)
            Srcs[key] = filename + ":" + str(lineno) + ": " + opt
    if len(Srcs) < 5:
        test.error("Didn't parse any options")
    return Srcs


def read_tests():
    filename = "test_regress/t/*.py"
    for filename in (test.glob_some(test.root + "/test_regress/t/*.py")):
        if "t_dist_docs_options" in filename:  # Avoid our own suppressions
            continue
        with open(filename, 'r', encoding="latin-1") as fh:
            lineno = 0
            for line in fh:
                lineno += 1
                line = line.lstrip().rstrip()
                for opt in re.findall(r'[-+]+[-+a-zA-Z0-9]+', line):
                    opt = opt_clean(opt)
                    key = opt_key(opt)
                    if test.verbose:
                        print("T '" + opt + "' " + line)
                    Tests[key] = filename + ":" + str(lineno) + ": " + opt
                    # For e.g. +verilator+seed+<something> and -dumpi-<#>
                    pos = max(opt.rfind('+'), opt.rfind('-'))
                    if pos > 1:
                        subkey = opt[:pos + 1]
                        if test.verbose:
                            print("t '" + subkey + "' " + line)
                        Tests[subkey] = filename + ":" + str(lineno) + ": " + opt


def opt_clean(opt):
    opt = re.sub(r'--', '-', opt)
    opt = re.sub(r'<.*', '', opt)
    opt = re.sub(r'\\', '', opt)
    return opt


def opt_key(opt):
    opt = opt_clean(opt)
    opt = re.sub(r'^-fno-', '-f', opt)
    opt = re.sub(r'^-no-', '-', opt)
    return opt


if not os.path.exists(test.root + "/.git"):
    test.skip("Not in a git repository")

read_sums()
read_docs()
read_srcs()
read_tests()

both = {}
both.update(Sums)
both.update(Docs)
both.update(Srcs)

doc_waiver = {k: 1 for k in Doc_Waivers}

for opt in sorted(both.keys()):
    if opt in doc_waiver:
        continue

    is_in = []
    not_in = []
    summ = None
    if opt in Sums:
        summ = Sums[opt]
        is_in.append("summary " + summ)
    else:
        if not re.match(r'-f', opt):
            not_in.append("ARGUMENT SUMMARY in bin/verilator or bin/verilator_coverage")

    doc = None
    if opt in Docs:
        doc = Docs[opt]
        is_in.append("documentation " + doc)
    else:
        not_in.append("documentation in docs/guide/exe_*.rst")

    src = None
    if opt in Srcs:
        src = Srcs[opt]
        is_in.append("sources " + src)
    # Ok if not in sources

    if opt in Tests:
        if opt in Test_Waivers:
            print("Unnecessary Test_Waiver for option: '" + opt + "'")

    else:
        if opt in Test_Waivers:
            is_in.append("Test_Waiver for test_regress/t/*.py")
        else:
            not_in.append("uncovered in test_regress/t/*.py")

    if not_in:
        test.error_keep_going("Option '" + opt + "' has inconsistent references\n" +
                              "  Missing in " + "\n  Missing in ".join(not_in) + "\n  Found in " +
                              "\n  Found in ".join(is_in))

test.passes()
