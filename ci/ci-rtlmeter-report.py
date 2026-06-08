# DESCRIPTION: Verilator: CI script for 'rtlmeter.yml' PR results
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

###############################################################################
# This script runs with the venv of **RTLMeter**
###############################################################################

import sys
import json
import tabulate
from typing import Final, List

tabulate.PRESERVE_WHITESPACE = True
tabulate.MIN_PADDING = 0

_ASCII_TABLE_FORMAT: Final = tabulate.TableFormat(
    lineabove=tabulate.Line("╒═", "═", "═╤═", "═╕"),
    linebelowheader=tabulate.Line("╞═", "═", "═╪═", "═╡"),
    linebelow=tabulate.Line("╘═", "═", "═╧═", "═╛"),
    headerrow=tabulate.DataRow("│ ", " │ ", " │"),
    datarow=tabulate.DataRow("│ ", " │ ", " │"),
    linebetweenrows=None,
    padding=0,
    with_header_hide=None,
)


def printTable(table: List[List[str]], **kwargs) -> None:
    print(tabulate.tabulate(table, tablefmt=_ASCII_TABLE_FORMAT, **kwargs))


# fmt: off
stepMetric = (
    # Step,      Metric,    Status Brackets
    ("execute",  "speed",   ("❌", 0.96, "⚠️", 0.98, "✅", 1.02, "💡", 1.04, "⭐")),
    ("execute",  "memory",  ("❌", 0.90, "⚠️", 0.95, "✅", 1.05, "💡", 1.10, "⭐")),
    ("verilate", "cpu",     ("❌", 0.96, "⚠️", 0.98, "✅", 1.02, "💡", 1.04, "⭐")),
    ("verilate", "memory",  ("❌", 0.90, "⚠️", 0.95, "✅", 1.05, "💡", 1.10, "⭐")),
    ("cppbuild", "cpu",     ("❌", 0.96, "⚠️", 0.98, "✅", 1.02, "💡", 1.04, "⭐")),
    ("cppbuild", "memory",  ("❌", 0.90, "⚠️", 0.95, "✅", 1.05, "💡", 1.10, "⭐")),
    ("cppbuild", "codeSize",("❌", 0.96, "⚠️", 0.98, "✅", 1.02, "💡", 1.04, "⭐")),
    ("cppbuild", "elapsed", ("❌", 0.70, "⚠️", 0.85, "✅", 1.15, "💡", 1.30, "⭐")),
)

badgeLegend = [
    ("❌", "Likely regression"),
    ("⚠️", "Possible regression"),
    ("✅", "Within acceptable range"),
    ("💡", "Possible improvement"),
    ("⭐", "Likely improvement"),
]
# fmt: on

changedCycles = []
table = []
badgesToExplain = set()

for ref, cmp in zip(sys.argv[1::2], sys.argv[2::2]):
    with open(ref, "r", encoding="utf-8") as f:
        ref_json = json.load(f)[0]
    with open(cmp, "r", encoding="utf-8") as f:
        cmp_json = json.load(f)
    if table:
        table.append(tabulate.SEPARATING_LINE)
    runName = ref_json["runName"]

    # Check simulated cycles match - it's ok to crash if this entry does not exist
    for entry in cmp_json["execute"]["clocks"]["table"]:
        case, _, _, (refCycles, _), (newCycles, _), _, _ = entry
        refCycles = int(refCycles)
        newCycles = int(newCycles)
        if refCycles != newCycles:
            changedCycles.append([runName, case, refCycles, newCycles])

    # Check metrics
    for step, metric, brackets in stepMetric:
        if step not in cmp_json:
            continue
        data = cmp_json[step]
        if metric not in data:
            continue
        data = data[metric]
        minGain = float("inf")
        maxGain = float("-inf")
        meanGain = 1
        count = 0
        for _, _, _, (a, _), (b, _), g, _ in data["table"]:
            # for wall clock and CPU time, ignore small values that just add noise
            if metric == "elapsed" or metric == "cpu":
                if a < 30 or b < 30:
                    continue
            minGain = min(minGain, g)
            maxGain = max(maxGain, g)
            meanGain *= g
            count += 1
        if count == 0:
            continue
        meanGain = meanGain**(1 / count)

        status = brackets[0]
        for limit, badge in zip(brackets[1::2], brackets[2::2]):
            if meanGain >= limit:
                status = badge
        badgesToExplain.add(status)

        table.append([
            runName, step, ref_json["metrics"][metric]["header"], f"{meanGain:.2f}x  {status} ",
            f"{minGain:.2f}x", f"{maxGain:.2f}x", f"{count}"
        ])

# Print changed cycles if any
if changedCycles:
    print("❌ simulated cycles changed (must be fixed):")
    printTable(changedCycles,
               headers=("Run", "Case", "Old Cycles", "New Cycles"),
               colalign=("left", "left", "right", "right"),
               disable_numparse=True)
    print()

# Print results
printTable(
    table,
    headers=("Run", "Step", "Metric", "Improvement", "Min", "Max", "Samples"),
    colalign=("left", "left", "left", "right", "right", "right", "right"),
    disable_numparse=True,
)

# Explain badges
print()
for badge, legend in badgeLegend:
    if badge in badgesToExplain:
        print(f"  {badge} : {legend}")

# Fail job if status changed
sys.exit(0 if not changedCycles else 1)
