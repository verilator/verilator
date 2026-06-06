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
    ("verilate", "elapsed"),
    ("verilate", "cpu"),
    ("verilate", "memory"),
    ("cppbuild", "elapsed"),
    ("cppbuild", "cpu"),
    ("cppbuild", "memory"),
    ("cppbuild", "codeSize"),
    ("execute", "elapsed"),
    ("execute", "speed"),
    ("execute", "cpu"),
    ("execute", "memory"),
    ("execute", "clocks")
)
# fmt: on

steps = ["verilate", "cppbuild", "execute"]
metics = ["elapsed", "speed", "cpu", "memory", "codeSize"]

table = []

for ref, cmp in zip(sys.argv[1::2], sys.argv[2::2]):
    with open(ref, "r", encoding="utf-8") as f:
        ref_json = json.load(f)[0]
    with open(cmp, "r", encoding="utf-8") as f:
        cmp_json = json.load(f)
    if table:
        table.append(tabulate.SEPARATING_LINE)
    runName = ref_json["runName"]
    for step, metric in stepMetric:
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
        for _, _, _, _, _, g, _ in data["table"]:
            minGain = min(minGain, g)
            maxGain = max(maxGain, g)
            meanGain *= g
            count += 1
        meanGain = meanGain**(1 / count)

        if metric == "clocks":
            # Clock cycles should match exactly
            status = "❌" if minGain != 1 or maxGain != 1 else "✅"
        else:
            # Otherwise use some arbitrary brackets
            status = "❌"
            if (meanGain > 0.95):
                status = "⚠️"
            if (meanGain > 0.98):
                status = "✅"
            if (meanGain > 1.02):
                status = "💡"
            if (meanGain > 1.05):
                status = "⭐"

        table.append([
            runName, step, ref_json["metrics"][metric]["header"], f"{meanGain:.2f}x  {status} ",
            f"{minGain:.2f}x", f"{maxGain:.2f}x"
        ])

printTable(
    table,
    headers=("Run", "Step", "Metric", "Improvement", "Min", "Max"),
    colalign=("left", "left", "left", "right", "right", "right"),
    disable_numparse=True,
)
