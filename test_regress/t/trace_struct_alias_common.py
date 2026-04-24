# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


def _vcd_extract_codes(filename):
    """Parse VCD header and return dict mapping 'scope.signal' -> code."""
    codes = {}
    scope_stack = []
    with open(filename, 'r', encoding='latin-1') as fh:
        for line in fh:
            line = line.strip()
            if line.startswith("$scope"):
                parts = line.split()
                # $scope <type> <name> $end
                scope_stack.append(parts[2])
            elif line.startswith("$var"):
                parts = line.split()
                # $var <type> <width> <code> <name> ... $end
                code = parts[3]
                name = parts[4]
                full = '.'.join(scope_stack) + '.' + name
                codes[full] = code
            elif line.startswith("$upscope"):
                scope_stack.pop()
            elif line.startswith("$enddefinitions"):
                break
    return codes


def _check_aliased(test, codes, sig_a, sig_b):
    code_a = codes.get(sig_a)
    code_b = codes.get(sig_b)
    if code_a is None:
        test.error(f"Signal '{sig_a}' not found in VCD")
    if code_b is None:
        test.error(f"Signal '{sig_b}' not found in VCD")
    if code_a != code_b:
        test.error(f"Expected '{sig_a}' (code {code_a}) to alias "
                   f"'{sig_b}' (code {code_b})")


def _check_not_aliased(test, codes, sig_a, sig_b):
    code_a = codes.get(sig_a)
    code_b = codes.get(sig_b)
    if code_a is None:
        test.error(f"Signal '{sig_a}' not found in VCD")
    if code_b is None:
        test.error(f"Signal '{sig_b}' not found in VCD")
    if code_a == code_b:
        test.error(f"Expected '{sig_a}' and '{sig_b}' to have different codes, "
                   f"both have code {code_a}")


def run(test):
    (fmt, ) = test.parse_name(r"t_trace_struct_alias_([a-z]+)")

    test.top_filename = "t/t_trace_struct_alias.v"
    test.golden_filename = test.py_filename.rpartition(fmt)[0] + fmt + ".out"

    flags = ["--cc", f"--trace-{fmt}", "--trace-structs"]

    test.compile(verilator_flags2=flags)

    test.execute()

    if fmt == "vcd":
        codes = _vcd_extract_codes(test.trace_filename)

        _check_not_aliased(test, codes, "top.t.s1.a", "top.t.s2.a")

        _check_aliased(test, codes, "top.t.s3.a", "top.t.alias_of_s3a")

        _check_aliased(test, codes, "top.t.s4.a", "top.t.s5.a")
        _check_aliased(test, codes, "top.t.s4.b", "top.t.s5.b")

        _check_aliased(test, codes, "top.t.s6.a", "top.t.source_val")

    test.trace_identical(test.trace_filename, test.golden_filename)

    test.passes()
