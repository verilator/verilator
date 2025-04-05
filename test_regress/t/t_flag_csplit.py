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


def check_splits():
    got1 = False
    gotSyms1 = False
    for filename in test.glob_some(test.obj_dir + "/*.cpp"):
        if re.search(r'Syms__1', filename):
            gotSyms1 = True
        elif re.search(r'__1', filename):
            got1 = True
    if not got1:
        test.error("No __1 split file found")
    if not gotSyms1:
        test.error("No Syms__1 split file found")


def check_no_all_file():
    for filename in test.glob_some(test.obj_dir + "/*.cpp"):
        if re.search(r'__ALL.cpp', filename):
            test.error("__ALL.cpp file found: " + filename)


def check_cpp(filename):
    size = os.path.getsize(filename)
    if test.verbose:
        print("  File %6d  %s\n" % (size, filename))
    funcs = []
    with open(filename, 'r', encoding="utf8") as fh:
        for line in fh:
            m = re.search(r'^(void|IData)\s+(.*::.*){', line)
            if not m:
                continue
            func = m.group(2)
            func = re.sub(r'\(.*$', '', func)
            if test.verbose:
                print("\tFunc " + func)
            if (re.search(r'(::_eval_initial_loop$', func) or re.search(r'::__Vconfigure$', func)
                    or re.search(r'::trace$', func) or re.search(r'::traceInit$', func)
                    or re.search(r'::traceFull$', func) or re.search(r'::final$', func)
                    or re.search(r'::prepareClone$', func) or re.search(r'::atClone$', func)):
                continue
            funcs.append(func)

    if len(funcs) > 0:
        test.error("Split had multiple functions in $filename\n\t" + "\n\t".join(funcs))


def check_gcc_flags(filename):
    with open(filename, 'r', encoding="utf8") as fh:
        for line in fh:
            line = line.rstrip()
            if test.verbose:
                print(":log: " + line)
            if re.search(r'' + test.vm_prefix + r'\S*\.cpp', line):
                filetype = "slow" if re.search(r'(Slow|Syms)', line) else "fast"
                opt = "fast" if re.search(r'-O2', line) else "slow"
                if test.verbose:
                    print(filetype + ", " + opt + ", " + line)
                if filetype != opt:
                    test.error(filetype + " file compiled as if was " + opt + ": " + line)
            elif re.search(r'.cpp', line) and not re.search(r'-Os', line):
                test.error("library file not compiled with OPT_GLOBAL: " + line)


# This rule requires GNU make > 4.1 (or so, known broken in 3.81)
#%__Slow.o: %__Slow.cpp
#        $(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_SLOW) -c -o $@ $<
if not test.make_version or float(test.make_version) < 4.1:
    test.skip("Test requires GNU Make version >= 4.1")

test.compile(v_flags2=["--trace-vcd",
                       "--output-split 1",
                       "--output-split-cfuncs 1",
                       "--exe",
                       "../" + test.main_filename],
             verilator_make_gmake=False)  # yapf:disable

# We don't use the standard test_regress rules, as want to test the rules
# properly build
test.run(logfile=test.obj_dir + "/vlt_gcc.log",
         tee=test.verbose,
         cmd=[os.environ["MAKE"],
              "-C " + test.obj_dir,
              "-f "+test.vm_prefix+".mk",
              "-j 4",
              "VM_PREFIX="+test.vm_prefix,
              "TEST_OBJ_DIR="+test.obj_dir,
              "CPPFLAGS_DRIVER=-D"+test.name.upper(),
              ("CPPFLAGS_DRIVER2=-DTEST_VERBOSE=1" if test.verbose else ""),
              "OPT_FAST=-O2",
              "OPT_SLOW=-O0",
              "OPT_GLOBAL=-Os",
              ])  # yapf:disable

test.execute()

# Splitting should set VM_PARALLEL_BUILDS to 1 by default
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "_classes.mk", r'VM_PARALLEL_BUILDS\s*=\s*1')
check_splits()
check_no_all_file()
check_gcc_flags(test.obj_dir + "/vlt_gcc.log")

test.passes()
