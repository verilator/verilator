#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = "t/t_flag_csplit.v"


def check_no_splits():
    for filename in test.glob_some(test.obj_dir + "/*.cpp"):
        filename = re.sub(r'__024root', '', filename)
        if re.search(r'__[1-9]', filename):
            test.error("Split file found: " + filename)


def check_all_file():
    for filename in test.glob_some(test.obj_dir + "/*.cpp"):
        if re.search(r'__ALL.cpp', filename):
            return


def check_gcc_flags(filename):
    with open(filename, 'r', encoding="utf8") as fh:
        for line in fh:
            line = line.rstrip()
            if test.verbose:
                print(":log: " + line)
            if re.search(r'\.cpp', line) and re.search('-O0', line):
                test.error("File built as slow (should be in __ALL.cpp) : " + line)


# This rule requires GNU make > 4.1 (or so, known broken in 3.81)
#%__Slow.o: %__Slow.cpp
#        $(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_SLOW) -c -o $@ $<
if not test.make_version or float(test.make_version) < 4.1:
    test.skip("Test requires GNU Make version >= 4.1")

test.compile(v_flags2=["--trace-vcd --output-split 0 --exe ../" + test.main_filename],
             verilator_make_gmake=False)

# We don't use the standard test_regress rules, as want to test the rules
# properly build
test.run(logfile=test.obj_dir + "/vlt_gcc.log",
         tee=test.verbose,
         cmd=[
             os.environ["MAKE"], "-C " + test.obj_dir, "-f " + test.vm_prefix + ".mk", "-j 4",
             "VM_PREFIX=" + test.vm_prefix, "TEST_OBJ_DIR=" + test.obj_dir,
             "CPPFLAGS_DRIVER=-D" + test.name.upper(),
             ("CPPFLAGS_DRIVER2=-DTEST_VERBOSE=1" if test.verbose else ""), "OPT_FAST=-O2",
             "OPT_SLOW=-O0"
         ])

test.execute()

# Never spliting, so should set VM_PARALLEL_BUILDS to 0 by default
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "_classes.mk", r'VM_PARALLEL_BUILDS\s*=\s*0')
check_no_splits()
check_all_file()
check_gcc_flags(test.obj_dir + "/vlt_gcc.log")

test.passes()
