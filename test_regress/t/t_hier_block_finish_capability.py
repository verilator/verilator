#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.priority(30)
test.scenarios('vlt_all')

test.clean_objs()

test.compile(
    v_flags2=['t/t_hier_block_finish_capability.cpp'],
    verilator_flags2=['--hierarchical', '--stats', 't/t_hier_block_finish_capability.vlt'],
    threads=(2 if test.vltmt else 1))


def require_certificates(module, wrappers):
    filename = test.obj_dir + "/V" + module + "/" + module + ".sv"
    for wrapper in wrappers:
        test.file_grep(filename,
                       r'no_finish -hier-dpi "' + module + '_protectlib_' + wrapper + r'"')


def reject_certificates(module, wrappers):
    filename = test.obj_dir + "/V" + module + "/" + module + ".sv"
    for wrapper in wrappers:
        test.file_grep_not(filename,
                           r'no_finish -hier-dpi "' + module + '_protectlib_' + wrapper + r'"')


all_wrappers = ("check_hash", "combo_ignore", "combo_update", "create", "final", "seq_update")
common_wrappers = ("check_hash", "combo_ignore", "create")
update_wrappers = ("combo_update", "seq_update")

require_certificates("NoFinish", all_wrappers)
require_certificates("UnusedClassFinish", all_wrappers)

for module in ("EvalFinish", "EvalClassFinish", "LeafFinish", "MiddleFinish"):
    require_certificates(module, common_wrappers + ("final", ))
    reject_certificates(module, update_wrappers)

require_certificates("FinalFinish", common_wrappers + update_wrappers)
reject_certificates("FinalFinish", ("final", ))
require_certificates("FinalClassFinish", common_wrappers + update_wrappers)
reject_certificates("FinalClassFinish", ("final", ))

for module, eval_may_finish, final_may_finish in (
    ("NoFinish", 0, 0),
    ("UnusedClassFinish", 0, 0),
    ("EvalFinish", 1, 0),
    ("EvalClassFinish", 1, 0),
    ("FinalFinish", 0, 1),
    ("FinalClassFinish", 0, 1),
    ("LeafFinish", 1, 0),
    ("MiddleFinish", 1, 0),
):
    child_stats = test.obj_dir + "/V" + module + "/V" + module + "__stats.txt"
    test.file_grep(child_stats, r'Finish, Hierarchical eval may finish\s+(\d+)', eval_may_finish)
    test.file_grep(child_stats, r'Finish, Hierarchical final may finish\s+(\d+)', final_may_finish)

parent_stats = test.obj_dir + "/V" + test.name + "__hier.dir/V" + test.name + "__stats.txt"
test.file_grep(parent_stats, r'Finish, Finish-capable calls\s+(\d+)', 8)
test.file_grep(parent_stats, r'Finish, Guards\s+(\d+)', 8)

for module, eval_may_finish in (
    ("AliasedCanonicalWrapper", 0),
    ("AliasedNearMissWrapper", 1),
):
    alias_obj_dir = test.obj_dir + "/" + module
    test.run(cmd=[
        os.environ["VERILATOR_ROOT"] +
        "/bin/verilator", "--cc", "--top-module", module, "--stats", "--Mdir", alias_obj_dir,
        "t/t_hier_block_finish_capability.v", "t/t_hier_block_finish_capability.vlt"
    ])
    alias_stats = alias_obj_dir + "/V" + module + "__stats.txt"
    test.file_grep(alias_stats, r'Finish, Hierarchical eval may finish\s+(\d+)', eval_may_finish)

for mode, marker in (
    ("EVAL", "EVAL_FINISH_EXECUTED"),
    ("NESTED", "NESTED_FINISH_EXECUTED"),
    ("FINAL", "FINAL_FINISH_EXECUTED"),
    ("CLASS_EVAL", "CLASS_EVAL_FINISH_EXECUTED"),
    ("CLASS_FINAL", "CLASS_FINAL_FINISH_EXECUTED"),
):
    logfile = test.obj_dir + "/sim_" + mode.lower() + ".log"
    test.execute(all_run_flags=["+" + mode], logfile=logfile)
    test.file_grep(logfile, marker)

test.passes()
