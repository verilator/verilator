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

root = ".."

Messages = {}
Outputs = {}
Suppressed = {}

for s in [
        ' exited with ',  # Is hit; driver.py filters out
        'EOF in unterminated string',  # Instead get normal unterminated
        'Enum ranges must be integral, per spec',  # Hard to hit
        'Import package not found: ',  # Errors earlier, until future parser released
        'Return with return value isn\'t underneath a function',  # Hard to hit, get other bad return messages
        'Syntax error: Range \':\', \'+:\' etc are not allowed in the instance ',  # Instead get syntax error
        'Syntax error parsing real: \'',  # Instead can't lex the number
        'Unsupported: Ranges ignored in port-lists',  # Hard to hit
        'dynamic new() not expected in this context (expected under an assign)',  # Instead get syntax error
        # Not yet analyzed
        ' loading non-variable',
        '--pins-bv maximum is 65: ',
        '--pipe-filter protocol error, unexpected: ',
        '--pipe-filter returned bad status',
        '--pipe-filter: Can\'t pipe: ',
        '--pipe-filter: fork failed: ',
        '--threads must be >= 0: ',
        '--threads-max-mtasks must be >= 1: ',
        '--trace-threads must be >= 1: ',
        '/*verilator sformat*/ can only be applied to last argument of ',
        'Argument needed for string.',
        'Array initialization has too few elements, need element ',
        'Assigned pin is neither input nor output',
        'Assignment pattern with no members',
        'Can\'t find varpin scope of ',
        'Can\'t read annotation file: ',
        'Can\'t resolve module reference: \'',
        'Can\'t write file: ',
        'Circular logic when ordering code (non-cutable edge loop)',
        'Define missing argument \'',
        'Define or directive not defined: `',
        'Exceeded limit of ',
        'Expecting define formal arguments. Found: ',
        'Extern declaration\'s scope is not a defined class',
        'File not found: ',
        'Format to $display-like function must have constant format string',
        'Forward typedef used as class/package does not resolve to class/package: ',
        'Illegal +: or -: select; type already selected, or bad dimension: ',
        'Illegal bit or array select; type already selected, or bad dimension: ',
        'Illegal range select; type already selected, or bad dimension: ',
        'Member selection of non-struct/union object \'',
        'Modport item is not a function/task: ',
        'Modport item is not a variable: ',
        'Modport item not found: ',
        'Modport not referenced as <interface>.',
        'Modport not referenced from underneath an interface: ',
        'Parameter type pin value isn\'t a type: Param ',
        'Parameter type variable isn\'t a type: Param ',
        'Pattern replication value of 0 is not legal.',
        'Signals inside functions/tasks cannot be marked forceable',
        'Slice size cannot be zero.',
        'Slices of arrays in assignments have different unpacked dimensions, ',
        'String of ',
        'Symbol matching ',
        'Unexpected connection to arrayed port',
        'Unmatched brackets in variable substitution in file: ',
        'Unsized numbers/parameters not allowed in streams.',
        'Unsupported RHS tristate construct: ',
        'Unsupported or syntax error: Unsized range in instance or other declaration',
        'Unsupported pullup/down (weak driver) construct.',
        'Unsupported tristate construct (not in propagation graph): ',
        'Unsupported tristate port expression: ',
        'Unsupported/unknown built-in dynamic array method ',
        'Unsupported: $bits for queue',
        'Unsupported: $c can\'t generate wider than 64 bits',
        'Unsupported: &&& expression',
        'Unsupported: +%- range',
        'Unsupported: +/- range',
        'Unsupported: 4-state numbers in this context',
        'Unsupported: Bind with instance list',
        'Unsupported: Concatenation to form ',
        'Unsupported: Modport clocking',
        'Unsupported: Modport dotted port name',
        'Unsupported: Modport export with prototype',
        'Unsupported: Modport import with prototype',
        'Unsupported: Only one PSL clock allowed per assertion',
        'Unsupported: Per-bit array instantiations ',
        'Unsupported: Public functions with >64 bit outputs; ',
        'Unsupported: Replication to form ',
        'Unsupported: Shifting of by over 32-bit number isn\'t supported.',
        'Unsupported: Signal strengths are unsupported ',
        'Unsupported: Size-changing cast on non-basic data type',
        'Unsupported: Slice of non-constant bounds',
        'Unsupported: Unclocked assertion',
        'Unsupported: Verilog 1995 deassign',
        'Unsupported: Verilog 1995 gate primitive: ',
        'Unsupported: [] dimensions',
        'Unsupported: \'default :/\' constraint',
        'Unsupported: \'{} .* patterns',
        'Unsupported: \'{} tagged patterns',
        'Unsupported: always[] (in property expression)',
        'Unsupported: assertion items in clocking blocks',
        'Unsupported: default clocking identifier',
        'Unsupported: don\'t know how to deal with ',
        'Unsupported: eventually[] (in property expression)',
        'Unsupported: extern forkjoin',
        'Unsupported: extern interface',
        'Unsupported: extern module',
        'Unsupported: extern task',
        'Unsupported: modport export',
        'Unsupported: no_inline for tasks',
        'Unsupported: property port \'local\'',
        'Unsupported: randsequence production list',
        'Unsupported: randsequence repeat',
        'Unsupported: repeat event control',
        'Unsupported: s_always (in property expression)',
        'Unsupported: static cast to ',
        'Unsupported: super',
        'Unsupported: this.super',
        'Unsupported: trireg',
        'Unsupported: with[] stream expression',
]:
    Suppressed[s] = True


def read_messages():
    for filename in test.glob_some(root + "/src/*"):
        if not os.path.isfile(filename):
            continue
        with open(filename, 'r', encoding="utf8") as fh:
            lineno = 0
            read_next = None

            for origline in fh:
                line = origline
                lineno += 1
                if re.match(r'^\s*//', line):
                    continue
                if re.match(r'^\s*/\*', line):
                    continue
                if re.search(r'\b(v3error|v3warn|v3fatal|BBUNSUP)\b\($', line):
                    if 'LCOV_EXCL_LINE' not in line:
                        read_next = True
                    continue
                m = re.search(r'.*\b(v3error|v3warn|v3fatal|BBUNSUP)\b(.*)', line)
                if m:
                    line = m.group(2)
                    if 'LCOV_EXCL_LINE' not in line:
                        read_next = True
                if read_next:
                    read_next = False
                    if 'LCOV_EXCL_LINE' in line:
                        continue
                    if "\\" in line:  # \" messes up next part
                        continue
                    m = re.search(r'"([^"]*)"', line)
                    if m:
                        msg = m.group(1)
                        fileline = filename + ":" + str(lineno)
                        # print("FFFF " + fileline + ": " + msg + "   LL " + line)
                        Messages[msg] = {}
                        Messages[msg]['fileline'] = fileline
                        Messages[msg]['line'] = origline

    print("Number of messages = " + str(len(Messages)))


def read_outputs():
    for filename in (test.glob_some(root + "/test_regress/t/*.py") +
                     test.glob_some(root + "/test_regress/t/*.out") +
                     test.glob_some(root + "/docs/gen/*.rst")):
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
    print("Coverage = %3.1f%%" % (100 - int(100 * len(Suppressed) / len(Messages))))
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


if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

check()

test.passes()

# Local Variables:
# compile-command:"./t_dist_warn_coverage.py"
# End:
