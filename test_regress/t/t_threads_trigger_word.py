#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.sim_time = 3000

test.compile(threads=(2 if test.vltmt else 1))

MASKED = r'\b(0x[0-9a-f]+|\d+)ULL & '
WORD = r'vlSelfRef\.__VnbaTriggered\[(\d+)U\]'
GROUP = MASKED + r'\(((?:\s*\|?\s*vlSelfRef\.__VnbaTriggered\[\d+U\])+)\)'


def tested_bits(name, funcs, seen):
    # Bits of each trigger word tested by a function, and by the functions it calls
    bits = {}
    if name in seen:
        return bits
    seen.add(name)

    def add(word, mask):
        bits[int(word)] = bits.get(int(word), 0) | mask

    body = funcs[name]
    for mask, words in re.findall(GROUP, body):  # 'mask & (word | word ...)'
        for word in re.findall(r'\[(\d+)U\]', words):
            add(word, int(mask, 0))
    for mask, word in re.findall('(?:' + MASKED + ')?' + WORD, re.sub(GROUP, '', body)):
        add(word, int(mask, 0) if mask else 2**64 - 1)
    for callee in re.findall(r'\b(\w+)\(', body):
        if callee in funcs:
            for word, mask in tested_bits(callee, funcs, seen).items():
                add(word, mask)
    return bits


if test.vltmt:
    # The exec graph lists every MTask once, with exactly the trigger bits its code tests
    text = "".join(
        test.file_contents(filename)
        for filename in test.glob_some(test.obj_dir + "/" + test.vm_prefix + "___024root*.cpp"))
    funcs = dict(re.findall(r'^void (\w+)\([^)]*\) \{\n(.*?)^\}', text, re.S | re.M))
    graph = re.search(r'__VexecGraph\{&\w+, __Vvertices, (\d+), (\w+), (\w+), (\d+)\}', text)
    vertices = re.findall(r'\{&(\w+), \d+, (\d+), (\d+)\}',
                          re.search(r'__Vvertices\[\] = \{(.*?)\};', text, re.S).group(1))
    masks = re.findall(r'\{(\d+), 0x([0-9a-f]+)ULL\}',
                       re.search(r'__Vmasks\[\] = \{(.*?)\};', text, re.S).group(1))
    edges = (re.findall(r'\{(\d+), (\d+)\}',
                        re.search(r'__Vedges\[\] = \{(.*?)\};', text, re.S).group(1))
             if graph.group(3) == '__Vedges' else [])
    if int(graph.group(1)) != len(vertices) or int(graph.group(4)) != len(edges):
        test.error("Exec graph counts do not match its tables")
    if sorted(func for func, _, _ in vertices) != sorted(f for f in funcs if '_mtask' in f):
        test.error("Exec graph vertices do not match the MTask functions")
    if any(int(a) >= int(b) or int(b) >= len(vertices) for a, b in edges):
        test.error("Exec graph edges are not in topological order")
    first = 0
    for func, start, count in vertices:
        if int(start) != first:
            test.error(func + ": trigger masks do not follow the previous MTask's")
        table = {int(w): int(b, 16) for w, b in masks[first:first + int(count)]}
        first += int(count)
        tested = tested_bits(func, funcs, set())
        if table != tested:
            test.error(func + ": table masks " + str(table) + ", but code tests " + str(tested))
    if first != len(masks):
        test.error("Exec graph has trigger masks of no MTask")

test.execute()

test.passes()
