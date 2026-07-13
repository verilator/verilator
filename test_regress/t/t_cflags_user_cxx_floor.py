#!/usr/bin/env python3
# DESCRIPTION: Verilator: user CFLAGS preserve the runtime C++ standard floor
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import shlex

import vltest_bootstrap

test.scenarios("vlt")
cxx_source = os.path.abspath("t/t_cflags_user_cxx_floor.cpp")
test.setenv("EXPECT_CXX_MIN", "201402L")
test.setenv("TEST_ENV_CXXFLAGS", "")
test.setenv("TEST_MAKE_CXXFLAGS", "-std=c++11")
user_object = "t_cflags_user_cxx_floor.o"
per_target_old_object = "t_cflags_user_cxx_floor_target_old.o"
per_target_new_object = "t_cflags_user_cxx_floor_target_new.o"
per_target_makefile = f"{test.obj_dir}/t_cflags_user_cxx_floor_targets.mk"

test.compile(
    verilator_flags2=[
        "--binary",
        "-CFLAGS",
        "'-DEXPECT_CXX_MIN=$(EXPECT_CXX_MIN) "
        "$(TEST_MAKE_CXXFLAGS) $${TEST_ENV_CXXFLAGS}'",
        cxx_source,
    ],
    verilator_make_gmake=False,
)

test.write_wholefile(
    per_target_makefile,
    f"""TEST_MAKE_CXXFLAGS = $(if $(filter {per_target_old_object},$@),-std=c++11,-std=c++17)
EXPECT_CXX_MIN = $(if $(filter {per_target_old_object},$@),201402L,201703L)
include {test.vm_prefix}.mk

{per_target_old_object}: {cxx_source}
{per_target_new_object}: {cxx_source} {per_target_old_object}
{per_target_old_object} {per_target_new_object}:
\t$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ {cxx_source}
""",
)


def compile_case(name, make_flags, env_flags="", min_cxx="201402L", fails=False):
    logfile = f"{test.obj_dir}/vlt_gcc_{name}.log"
    cmd = [
        "env",
        "TEST_ENV_CXXFLAGS=" + shlex.quote(env_flags),
        os.environ["MAKE"],
        "-B",
        "-C " + test.obj_dir,
        "-f " + test.vm_prefix + ".mk",
        "VM_PREFIX=" + test.vm_prefix,
        "EXPECT_CXX_MIN=" + min_cxx,
        "TEST_MAKE_CXXFLAGS=" + shlex.quote(make_flags),
        user_object,
    ]
    test.run(
        logfile=logfile,
        tee=test.verbose,
        fails="any" if fails else False,
        cmd=cmd,
    )


compile_case("cxx98", "-std=c++98")
compile_case("ansi", "-ansi")
compile_case("ansi_then_new", "-ansi -std=c++17", min_cxx="201703L")
compile_case("new_then_ansi", "-std=c++17 -ansi")
compile_case("cxx11", "-std=c++11")
compile_case("cxx14", "-std=c++14")
compile_case("cxx17", "-std=c++17", min_cxx="201703L")
compile_case("last_old", "-std=c++17", env_flags="-std=c++11")
compile_case(
    "last_new",
    "-std=c++11",
    env_flags="-std=c++17",
    min_cxx="201703L",
)
compile_case(
    "macro",
    "-DKEEP=-std=c++11 -std=c++17",
    min_cxx="201703L",
)
compile_case("invalid", "-std=c++11junk", fails=True)
test.run(
    logfile=f"{test.obj_dir}/vlt_gcc_per_target.log",
    tee=test.verbose,
    cmd=[
        os.environ["MAKE"],
        "-B",
        "-C " + test.obj_dir,
        "-f " + os.path.basename(per_target_makefile),
        "VM_PREFIX=" + test.vm_prefix,
        per_target_new_object,
    ],
)
test.execute()

test.passes()
