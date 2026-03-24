#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 by Wilson Snyder.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import re


_SHARED_TOP = "t/t_trace_dumpvars.v"
_SHARED_CPPTOP = "t/t_trace_dumpvars_cpptop.cpp"

_COMPILE_FAIL_CASES = {
    "cpptop2",
    "cpptop_missing2",
    "missing_scope",
    "missing2",
    "missing3",
    "missing4",
    "missing5",
    "t",
}

_EXECUTE_FAIL_CASES = {
    "cpptop_missing",
    "cpptop_missing3",
    "cpptop_missing4",
}

_CPPTOP_CASES = {
    "cpptop",
    "cpptop2",
    "cpptop_hier_array",
    "cpptop_hier_array_oob",
    "cpptop_hier_global",
    "cpptop_hier_struct",
    "cpptop_hier_struct2",
    "cpptop_missing",
    "cpptop_missing2",
    "cpptop_missing3",
    "cpptop_missing4",
}

_STRUCT_TRACE_CASES = {
    "struct",
    "hier_struct",
    "cpptop_hier_struct",
    "cpptop_hier_struct2",
}

_NO_INLINE_CASES = {
    "hier_global_task",
    "task_no_inl",
    "task2_no_inl",
}

_FILE_COMPARE_CASES = {
    "cpptop_hier_array_oob",
}

_DEFINE_ALIASES = {
    "cpptop_hier_global": "hier_global",
    "task_no_inl": "task",
    "task2_no_inl": "task2",
}


def _case_name(test):
    name = os.path.splitext(os.path.basename(test.py_filename))[0]
    prefix = "t_trace_dumpvars"
    if name == prefix:
        return "base"
    if not name.startswith(prefix + "_"):
        test.error(f"Invalid trace dumpvars test file '{name}'")
    return name[len(prefix) + 1:]


def _define_name(case):
    define_case = _DEFINE_ALIASES.get(case, case)
    token = re.sub(r"[^0-9A-Za-z]+", "_", define_case).upper()
    return f"+define+TRACE_DUMPVARS_CASE_{token}"


def _compile_flags(case):
    flags = ["--top-module", "t", _define_name(case)]
    if case == "add_module":
        flags = ["--binary", "--timing", "--trace-vcd", *flags]
    elif case in _CPPTOP_CASES:
        flags = ["--cc", "--exe", "--trace-vcd", *flags, _SHARED_CPPTOP]
    else:
        flags = ["--binary", "--trace-vcd", *flags]

    if case in _STRUCT_TRACE_CASES:
        flags.append("--trace-structs")
    if case in _NO_INLINE_CASES:
        flags.append("--fno-inline")
    return flags


def _has_golden_trace(test):
    return os.path.exists(test.golden_filename) and os.path.getsize(test.golden_filename) > 0


def run(test):
    case = _case_name(test)
    if case == "top":
        test.passes()
        return

    test.top_filename = _SHARED_TOP
    compile_kwargs = {"verilator_flags2": _compile_flags(case)}
    if case in _CPPTOP_CASES:
        compile_kwargs["make_main"] = False

    if case in _COMPILE_FAIL_CASES:
        test.compile(fails=True, expect_filename=test.golden_filename, **compile_kwargs)
        test.passes()
        return

    test.compile(**compile_kwargs)

    if case in _EXECUTE_FAIL_CASES:
        test.execute(fails=True, expect_filename=test.golden_filename)
        test.passes()
        return

    execute_kwargs = {}
    if case == "nonconst_scope":
        execute_kwargs["all_run_flags"] = ['+LEVEL=0']

    test.execute(**execute_kwargs)

    if case == "add_module":
        test.vcd_identical(test.obj_dir + "/simx0.vcd",
                           test.t_dir + "/t_trace_dumpvars_add_module_0.out")
        test.vcd_identical(test.obj_dir + "/simx1.vcd",
                           test.t_dir + "/t_trace_dumpvars_add_module_1.out")
    elif _has_golden_trace(test):
        if case in _FILE_COMPARE_CASES:
            test.files_identical(test.trace_filename, test.golden_filename)
        else:
            test.vcd_identical(test.trace_filename, test.golden_filename)

    test.passes()
