#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import re
import os

test.scenarios('simulator')

test.compile(verilator_flags2=['--trace'])

test.execute()

# Test that expressions are NOT inlined into trace update functions to avoid code repetition

trace_full_file = test.obj_dir + "/" + test.vm_prefix + "__Trace__0__Slow.cpp"
trace_chg_file = test.obj_dir + "/" + test.vm_prefix + "__Trace__0.cpp"

if test.vlt_all:
    if os.path.exists(trace_full_file):
        with open(trace_full_file, 'r', encoding="utf-8") as f:
            trace_content = f.read()

        # Search for inlined expressions, e.g.: bufp->fullBit(oldp+X,((1U & (~ (IData)(vlSelfRef.clk)))));
        inlined_not = re.findall(r'fullBit\([^)]*\(\(1U & \(\~', trace_content)
        inlined_arithmetic = re.findall(r'fullCData\([^)]*\(\(.*\+.*\)', trace_content)
        complex_inlined = re.findall(r'full(?:CData|SData)\([^)]*\([^)]*\+[^)]*\)\s*\*',
                                     trace_content)
        deeply_nested_inlined = re.findall(r'full(?:IData|QData)\([^)]*\{[^}]*\{[^}]*\}',
                                           trace_content)

        if len(inlined_not) > 0:
            test.error(f"Found {len(inlined_not)} inlined NOT expressions in trace full functions")

        if len(inlined_arithmetic) > 0:
            test.error(
                f"Found {len(inlined_arithmetic)} inlined arithmetic expressions in trace full functions"
            )

        if len(complex_inlined) > 0:
            test.error(
                f"Found {len(complex_inlined)} complex inlined multiplication expressions in trace full functions"
            )

        if len(deeply_nested_inlined) > 0:
            test.error(
                f"Found {len(deeply_nested_inlined)} deeply nested inlined expressions in trace full functions"
            )

        # Search for variable references
        var_refs_simple = re.findall(
            r'fullBit\(oldp\+\d+,\(vlSelfRef\.t__DOT__.*__DOT__simple_not\)\)', trace_content)
        var_refs_add = re.findall(
            r'fullCData\(oldp\+\d+,\(vlSelfRef\.t__DOT__.*__DOT__add_result\)', trace_content)
        var_refs_mul = re.findall(
            r'fullCData\(oldp\+\d+,\(vlSelfRef\.t__DOT__.*__DOT__mul_result\)', trace_content)

        if len(var_refs_simple) == 0:
            test.error(
                "No variable references found for simple_not signal in trace code - expressions are probably inlined instead"
            )

        if len(var_refs_add) == 0:
            test.error(
                "No variable references found for add_result signal in trace code - expressions are probably inlined instead"
            )

        if len(var_refs_mul) == 0:
            test.error(
                "No variable references found for mul_result signal in trace code - expressions are probably inlined instead"
            )

    # Check `chg` functions
    if os.path.exists(trace_chg_file):
        with open(trace_chg_file, 'r', encoding='utf-8') as f:
            trace_chg_content = f.read()

        # Search for inlined expressions, e.g.: chgBit(oldp+X,((1U & (~ ...))))
        chg_inlined_not = re.findall(r'chgBit\([^)]*\(\(1U & \(\~', trace_chg_content)
        chg_inlined_arith = re.findall(r'chgCData\([^)]*\(\(.*\+.*\)', trace_chg_content)

        if len(chg_inlined_not) > 0:
            test.error(
                f"Found {len(chg_inlined_not)} inlined NOT expressions in trace chg functions")

        if len(chg_inlined_arith) > 0:
            test.error(
                f"Found {len(chg_inlined_arith)} inlined arithmetic expressions in trace chg functions"
            )

test.passes()
