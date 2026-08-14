#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilator skills source-alignment verification
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import re
import sys
import subprocess
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import vltest_bootstrap

REPO_ROOT = Path(__file__).resolve().parent.parent.parent


def grep_count(pattern, path):
    """Return number of lines matching pattern under path (src/headers/grammar)."""
    try:
        result = subprocess.run(
            ["grep", "-rE", pattern, path, "--include=*.h", "--include=*.cpp",
             "--include=*.y", "--include=*.l"],
            capture_output=True, text=True
        )
        return len(result.stdout.strip().splitlines())
    except Exception:
        return 0


def check(cond, label):
    if cond:
        test.print(f"PASS: {label}")
        return True
    test.print(f"FAIL: {label}")
    return False


def main():
    all_ok = True

    # V3Stats API (skills reference V3Stats::addStat, not V3Stats::add)
    all_ok &= check(grep_count(r"V3Stats::addStat\(", "src") > 0,
                    "V3Stats::addStat exists in source")

    # VNUser guards: VNUser1InUse..VNUser4InUse exist; VNUser5InUse does NOT
    all_ok &= check(grep_count(r"class VNUser1InUse\b", "src") > 0, "VNUser1InUse exists")
    all_ok &= check(grep_count(r"class VNUser2InUse\b", "src") > 0, "VNUser2InUse exists")
    all_ok &= check(grep_count(r"class VNUser3InUse\b", "src") > 0, "VNUser3InUse exists")
    all_ok &= check(grep_count(r"class VNUser4InUse\b", "src") > 0, "VNUser4InUse exists")
    all_ok &= check(grep_count(r"class VNUser5InUse\b", "src") == 0,
                    "VNUser5InUse does NOT exist (skills must not reference it)")

    # VMemberMap / findMember
    all_ok &= check(grep_count(r"class VMemberMap\b", "src") > 0, "VMemberMap class exists")
    all_ok &= check(grep_count(r"findMember\(", "src") > 0,
                    "VMemberMap::findMember exists")

    # Casting macros
    all_ok &= check(grep_count(r"\bVN_CAST\b", "src") > 0, "VN_CAST macro exists")
    all_ok &= check(grep_count(r"\bVN_IS\b", "src") > 0, "VN_IS macro exists")
    all_ok &= check(grep_count(r"\bVN_AS\b", "src") > 0, "VN_AS macro exists")

    # Deferred deletion
    all_ok &= check(grep_count(r"\bVL_DO_DANGLING\b", "src") > 0, "VL_DO_DANGLING macro exists")
    all_ok &= check(grep_count(r"pushDeletep\(", "src") > 0, "pushDeletep() exists")

    # AST node methods
    all_ok &= check(grep_count(r"skipRefp\(", "src") > 0, "skipRefp() exists")
    all_ok &= check(grep_count(r"dumpJson\(", "src") > 0, "dumpJson() exists")
    all_ok &= check(grep_count(r"isSame\(", "src") > 0, "isSame() exists")
    all_ok &= check(grep_count(r"cloneRelink\(", "src") > 0, "cloneRelink() exists")
    all_ok &= check(grep_count(r"iterateAndNextNull\(", "src") > 0, "iterateAndNextNull() exists")

    # VL_* annotations
    all_ok &= check(grep_count(r"\bVL_RESTORER\b", "src") > 0, "VL_RESTORER macro exists")
    all_ok &= check(grep_count(r"\bVL_PURE\b", "src") > 0, "VL_PURE annotation exists")
    all_ok &= check(grep_count(r"\bVL_MT_SAFE\b", "src") > 0, "VL_MT_SAFE annotation exists")
    all_ok &= check(grep_count(r"\bVL_MT_STABLE\b", "src") > 0, "VL_MT_STABLE annotation exists")

    # Fixed-width types (in include/, not src/)
    all_ok &= check(grep_count(r"\bCData\b", "include") > 0, "CData type exists")
    all_ok &= check(grep_count(r"\bSData\b", "include") > 0, "SData type exists")
    all_ok &= check(grep_count(r"\bIData\b", "include") > 0, "IData type exists")
    all_ok &= check(grep_count(r"\bQData\b", "include") > 0, "QData type exists")
    all_ok &= check(grep_count(r"\bVlWide\b", "include") > 0, "VlWide type exists")

    # V3Number
    all_ok &= check(grep_count(r"class V3Number\b", "src") > 0, "V3Number class exists")

    # Graph classes
    all_ok &= check(grep_count(r"class V3Graph\b", "src") > 0, "V3Graph class exists")
    all_ok &= check(grep_count(r"class DfgGraph\b", "src") > 0, "DfgGraph class exists")

    # Runtime print helper (skills reference vl_print_warn_error)
    all_ok &= check(grep_count(r"vl_print_warn_error\(", "include") > 0,
                    "vl_print_warn_error() exists in include/")

    # Option API: DECL_OPTION is a local variable, not a macro;
    # notForRerun/undocumented are virtual methods on the option parser helper.
    all_ok &= check(grep_count(r"DECL_OPTION", "src") > 0,
                    "DECL_OPTION referenced in V3Options.cpp")
    all_ok &= check(grep_count(r"notForRerun\(\)", "src") > 0,
                    "notForRerun() method exists on option parser helper")
    all_ok &= check(grep_count(r"undocumented\(\)", "src") > 0,
                    "undocumented() method exists on option parser helper")

    # Key passes (V3Sched and V3Dfg are namespaces, not classes)
    key_passes = ["V3Width", "V3LinkDot", "V3Param", "V3Const", "V3Randomize",
                  "V3Assert", "V3Timing"]
    for cls in key_passes:
        all_ok &= check(grep_count(rf"class {cls}\b", "src") > 0, f"{cls} class exists")
    # V3Sched / V3Dfg are namespaces - check header declares them
    all_ok &= check(grep_count(r"namespace V3Sched\b", "src") > 0, "V3Sched namespace exists")
    all_ok &= check(grep_count(r"namespace V3Dfg\b", "src") > 0, "V3Dfg namespace exists")

    # Grammar tokens: real names are yOR / yAND (not OR_OP / AND_OP)
    all_ok &= check(grep_count(r"%left\s+yOR", "src") > 0,
                    "verilog.y uses yOR token (not OR_OP)")
    all_ok &= check(grep_count(r"%left\s+yAND", "src") > 0,
                    "verilog.y uses yAND token (not AND_OP)")

    # Test harness path
    all_ok &= check((REPO_ROOT / "test_regress" / "t" / "vltest_bootstrap.py").exists(),
                    "test_regress/t/vltest_bootstrap.py exists")

    if all_ok:
        test.print("All skill/source alignment checks passed")
        test.passes()
    else:
        test.error("Skill/source alignment checks failed; skills reference stale APIs")


if __name__ == "__main__":
    main()
