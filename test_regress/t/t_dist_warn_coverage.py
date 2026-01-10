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

Messages = {}
Outputs = {}
Suppressed = {}

for s in [
        # Cannot hit, and comment as to why
        # Instead of adding here, consider adding a LCOV_EXCL_LINE/START/STOP to the sources on the message
        'exited with',  # Is hit; driver.py filters out
        'loading non-variable',  # Instead 'storing to parameter' or syntax error
        'Assigned pin is neither input nor output',  # Instead earlier error
        'Define missing argument \'',  # Instead get Define passed too many arguments
        'Define or directive not defined: `',  # Instead V3ParseImp will warn
        'Expecting define formal arguments. Found:',  # Instead define syntax error
        'Syntax error: Range \':\', \'+:\' etc are not allowed in the instance',  # Instead get syntax error
        'dynamic new() not expected in this context (expected under an assign)',  # Instead get syntax error
        # Not yet analyzed
        '$VERILATOR_ROOT needs to be in environment',
        '--pipe-filter protocol error, unexpected:',
        '--pipe-filter returned bad status',
        '--pipe-filter: stdin/stdout closed before pipe opened',
        '--pipe-filter: write to closed file',
        'Assigning >32 bit to unranged parameter (defaults to 32 bits)',
        'Assignment pattern with no members',
        '%%Warning: DPI C Function called by Verilog DPI import with missing',
        '%%Warning: DPI svOpenArrayHandle function called on',
        '%%Warning: DPI svOpenArrayHandle function index 1',
        '%%Warning: DPI svOpenArrayHandle function index 2',
        '%%Warning: DPI svOpenArrayHandle function index 3',
        '%s : callback data pointer is null',
        '%s: Could not retrieve value of signal \'%s\' with',
        '%s: Ignoring vpi_put_value to vpiConstant: %s',
        '%s: Ignoring vpi_put_value to vpiParameter: %s',
        '%s: Non hex character \'%c\' in \'%s\' as value %s for %s',
        '%s: Non octal character \'%c\' in \'%s\' as value %s for %s',
        '%s: Parsing failed for \'%s\' as value %s for %s',
        '%s: Signal \'%s\' is marked forceable, but force',
        '%s: Signal \'%s\' with vpiHandle \'%p\' is marked forceable, but force',
        '%s: Trailing garbage \'%s\' in \'%s\' as value %s for %s',
        '%s: Unsupported callback type %s',
        '%s: Unsupported flags (%x)',
        '%s: Unsupported format (%s) as requested for %s',
        '%s: Unsupported format (%s) for %s',
        '%s: Unsupported p_vpi_value as requested for \'%s\' with vpiInertialDelay',
        '%s: Unsupported property %s, nothing will be returned',
        '%s: Unsupported type %s, ignoring',
        '%s: Unsupported type %s, nothing will be returned',
        '%s: Unsupported type (%d)',
        '%s: Unsupported type (%p, %s)',
        '%s: Unsupported vltype (%d)',
        '%s: Unsupported vpiHandle (%p)',
        '%s: Unsupported vpiHandle (%p) for type %s, nothing will be returned',
        '%s: Unsupported vpiUserAllocFlag (%x)',
        '%s: index %u for object %s is out of bounds [%u,%u]',
        '%s: requested elements (%u) exceed array size (%u)',
        '%s: requested elements to set (%u) exceed array size (%u)',
        '%s: vpi force or release requested for \'%s\', but vpiHandle \'%p\' of enable',
        '%s: vpi force or release requested for \'%s\', but vpiHandle \'%p\' of value',
        'Ignoring vpi_get_time with nullptr value pointer',
        'Ignoring vpi_get_value_array with null index pointer',
        'Ignoring vpi_get_value_array with null value pointer',
        'Ignoring vpi_put_value with nullptr value pointer',
        'Ignoring vpi_put_value_array to signal marked read-only,',
        'Ignoring vpi_put_value_array with null index pointer',
        'Ignoring vpi_put_value_array with null value pointer',
        'vpi_get_value with more than VL_VALUE_STRING_MAX_WORDS; increase and',
        'vpi_put_value was used on signal marked read-only,',
        'Can\'t find varpin scope of',
        'Can\'t read annotation file:',
        'Can\'t resolve module reference: \'',
        'Can\'t write file:',
        'Circular logic when ordering code (non-cutable edge loop)',
        'Expected data type, not a',
        'Extern declaration\'s scope is not a defined class',
        'File not found:',
        'Format to $display-like function must have constant format string',
        'Forward typedef used as class/package does not resolve to class/package:',
        'Illegal +: or -: select; type already selected, or bad dimension:',
        'Illegal bit or array select; type already selected, or bad dimension:',
        'Illegal range select; type already selected, or bad dimension:',
        'Instance pin connected by name with empty reference:',
        'Interface port declaration',
        'Invalid reference: Process might outlive variable',
        'Modport item is not a function/task:',
        'Modport item is not a variable:',
        'Modport not referenced as <interface>.',
        'Modport not referenced from underneath an interface:',
        'Need $SYSTEMC_INCLUDE in environment or when Verilator configured,',
        'Non-interface used as an interface:',
        'Parameter type pin value isn\'t a type: Param',
        'Parameter type variable isn\'t a type: Param',
        'Pattern replication value of 0 is not legal.',
        'Signals inside functions/tasks cannot be marked forceable',
        'Slice size cannot be zero.',
        'Slices of arrays in assignments have different unpacked dimensions,',
        'String of',
        'Symbol matching',
        'Unexpected connection to arrayed port',
        'Unsized numbers/parameters not allowed in streams.',
        'Unsupported (or syntax error): Foreach on this array\'s construct',
        'Unsupported LHS node type in array assignment',
        'Unsupported RHS tristate construct:',
        'Unsupported or syntax error: Unsized range in instance or other declaration',
        'Unsupported pullup/down (weak driver) construct.',
        'Unsupported tristate construct (not in propagation graph):',
        'Unsupported tristate port expression:',
        'Unsupported/unknown built-in queue method',
        'Unsupported: $bits for queue',
        'Unsupported: &&& expression',
        'Unsupported: 4-state numbers in this context',
        'Unsupported: Assignments with signal strength with LHS of type:',
        'Unsupported: Bind with instance list',
        'Unsupported: Cast to',
        'Unsupported: Concatenation to form',
        'Unsupported: Creating tristate signal not underneath a module:',
        'Unsupported: Default value on module inout/ref/constref:',
        'Unsupported: Modport empty expression',
        'Unsupported: Modport export with prototype',
        'Unsupported: Modport import with prototype',
        'Unsupported: Non-constant default value in missing argument',
        'Unsupported: Non-constant index when passing interface to module',
        'Unsupported: Only one PSL clock allowed per assertion',
        'Unsupported: Per-bit array instantiations',
        'Unsupported: Public functions with >64 bit outputs;',
        'Unsupported: Public functions with return > 64 bits wide.',
        'Unsupported: Release statement argument is too complex array select',
        'Unsupported: Replication to form',
        'Unsupported: Shifting of by over 32-bit number isn\'t supported.',
        'Unsupported: Size-changing cast on non-basic data type',
        'Unsupported: Slice of non-constant bounds',
        'Unsupported: Stream operation on a variable of a type',
        'Unsupported: Unclocked assertion',
        'Unsupported: Using --protect-ids with public function',
        'Unsupported: Verilog 1995 deassign',
        'Unsupported: Verilog 1995 gate primitive:',
        'Unsupported: [] dimensions',
        'Unsupported: \'default :/\' constraint',
        'Unsupported: \'{} .* patterns',
        'Unsupported: assertion items in clocking blocks',
        'Unsupported: don\'t know how to deal with',
        'Unsupported: extern constraint definition with class-in-class',
        'Unsupported: extern forkjoin',
        'Unsupported: extern task',
        'Unsupported: modport export',
        'Unsupported: no_inline for tasks',
        'Unsupported: non-const assert directive type expression',
        'Unsupported: property port \'local\'',
        'Unsupported: randsequence production function variable',
        'Unsupported: repeat event control',
        'Unsupported: static cast to',
        'Unsupported: super',
        'Unsupported: with[] stream expression',
        'expected non-complex non-double',
        'is not an unpacked array, but is in an unpacked array context',
        'loading other than unpacked-array variable',
        'loading other than unpacked/associative-array variable',
]:
    Suppressed[s] = True


def read_messages():
    for filename in (test.glob_some(test.root + "/src/*") +
                     test.glob_some(test.root + "/include/*")):
        if not os.path.isfile(filename):
            continue
        if '#' in filename:
            continue
        with open(filename, 'r', encoding="utf8") as fh:
            lineno = 0
            statement = ""
            statement_lineno = 0
            excl = False
            excl_next = False

            for origline in fh:
                line = origline
                lineno += 1
                if re.match(r'^\s*//', line):
                    continue
                if re.match(r'^\s*/\*', line):
                    continue
                excl = excl_next
                # print(('C ' if (statement != "") else 'L') + line)

                if 'LCOV_EXCL_START' in line:
                    excl = True
                    excl_next = True
                if 'LCOV_EXCL_STOP' in line:
                    excl_next = False  # Reenables coverage on next line, not this one
                if 'LCOV_EXCL_LINE' in line:
                    excl = True
                if excl:
                    statement = ""
                    continue

                line = re.sub(r'\\n', '', line)
                line = re.sub(r'\s+//.*', '', line)
                line = line.rstrip()

                m = re.search(
                    r'\b((v3error|v3warn|v3fatal|BBUNSUP|VL_FATAL|VL_FATAL_MT|VL_SVDPI_WARN_|VL_WARN|VL_WARN_MT|VL_VPI_ERROR_|VL_VPI_WARNING_)\b.*)',
                    line)
                if m:
                    statement = m.group(1)
                    statement_lineno = lineno

                if statement == "":
                    continue
                statement += line

                if ');' not in statement:
                    continue  # Keep reading lines until get end of statement

                if '\\"' in statement:
                    continue  # Parser messes these up

                # print("SSS " + statement)

                m = re.search(r'"([^"]*)"', statement)
                if m:
                    msg = m.group(1)
                    msg = re.sub(r'\s+$', '', msg)
                    msg = re.sub(r'^\s+', '', msg)
                    fileline = filename + ":" + str(statement_lineno)
                    # print("FFFF " + fileline + ": " + msg + "   LL " + statement)
                    Messages[msg] = {}
                    Messages[msg]['fileline'] = fileline
                    Messages[msg]['line'] = statement

                statement = ""

    print("Number of messages = " + str(len(Messages)))


def read_outputs():
    for filename in (test.glob_some(test.root + "/test_regress/t/*.py") +
                     test.glob_some(test.root + "/test_regress/t/*.out") +
                     test.glob_some(test.root + "/docs/gen/*.rst")):
        if "t_dist_warn_coverage" in filename:  # Avoid our own suppressions
            continue
        with open(filename, 'r', encoding="latin-1") as fh:
            for line in fh:
                if re.match(r'^\$date', line):  # Assume it is a VCD file
                    break
                line = line.lstrip().rstrip()
                Outputs[line] = True

    print("Number of outputs = " + str(len(Outputs)))


def check():
    read_messages()
    read_outputs()

    print("Number of suppressions = " + str(len(Suppressed)))
    print("Coverage = %3.1f%%" % (100 - (100 * len(Suppressed) / len(Messages))))
    print()

    print("Checking for v3error/v3warn messages in sources without")
    print("coverage in test_regress/t/*.out:")
    print("(Developers: If a message is impossible to test, consider using")
    print("UASSERT or v3fatalSrc instead of v3error)")
    print()

    used_suppressed = {}

    for msg in sorted(Messages.keys()):
        fileline = Messages[msg]['fileline']
        next_msg = False
        for output in Outputs:
            if msg in output:
                # print(fileline+": M '" + msg + "' HIT '" + output)
                next_msg = True
                break

        if next_msg:
            continue

        # Some exceptions
        if re.match(r'internal:', msg, re.IGNORECASE):
            continue

        line = Messages[msg]['line']
        line = line.lstrip().rstrip()

        if msg in Suppressed:
            used_suppressed[msg] = True
            if test.verbose:
                print(fileline + ": Suppressed check for message in source: '" + msg + "'")
        else:
            test.error_keep_going(fileline +
                                  ": Missing test_regress/t/*.out test for message in source: '" +
                                  msg + "'")
            if test.verbose:
                print("  Line is: " + line)

    print()
    for msg in sorted(Suppressed.keys()):
        if msg not in used_suppressed:
            print("Suppression not used: '" + msg + "'")
    print()


if not os.path.exists(test.root + "/.git"):
    test.skip("Not in a git repository")

check()

test.passes()

# Local Variables:
# compile-command:"./t_dist_warn_coverage.py"
# End:
