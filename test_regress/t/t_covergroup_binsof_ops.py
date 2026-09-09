#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import coverage_covergroup_common

test.scenarios('vlt_all')

coverage_covergroup_common.run(test,
                               verilator_flags2=[
                                   '--debug-self-test', '--dump-tree', '--dump-tree-json',
                                   '-CFLAGS -std=c++14'
                               ],
                               threads=(2 if test.vltmt else 1))

tree_files = test.glob_some(test.obj_dir + '/*.tree')
json_files = test.glob_some(test.obj_dir + '/*.tree.json')
test.file_grep_any(tree_files, r'COVERBINSOF.*\[NEGATED\]')
test.file_grep_any(tree_files, r'COVERCROSSSELECT.*\[AND\]')
test.file_grep_any(tree_files, r'COVERCROSSSELECT.*\[OR\]')
test.file_grep_any(json_files, r'"type":"COVERBINSOF".*"isNegated":true')
test.file_grep_any(json_files, r'"type":"COVERCROSSSELECT".*"isOr":true')

merged = test.obj_dir + '/merged.dat'
test.run(cmd=[
    os.environ['VERILATOR_ROOT'] + '/bin/verilator_coverage', '--write', merged,
    test.coverage_filename
],
         verilator_run=True)
test.file_grep(merged, r"cg_sets\.logic_ops\.not_hit_negation.*' 8")
test.file_grep(merged, r"cg_sets\.logic_ops\.named_not_hit.*' 16")
test.file_grep(merged, r"cg_sets\.logic_ops\.named_not_miss.*' 20")
test.file_grep(merged, r"cg_precedence\.three_axes\.ungrouped.*' 5")
test.file_grep(merged, r"cg_precedence\.three_axes\.grouped.*' 3")
test.file_grep(merged, r"cg_precedence\.three_axes\.mixed.*' 4")
test.file_grep(merged, r"cg_fast_paths\.selected\.early_a.*' 7")
test.file_grep(merged, r"cg_fast_paths\.selected\.early_b.*' 7")
test.file_grep(merged, r"cg_fast_paths\.selected\.late.*' 2")
test.file_grep(merged, r"cg_fast_paths\.selected\.first_x_second_x_first.*' 7")
test.file_grep(merged, r"cg_numeric\.numeric\.typed_negative.*' 2")
test.file_grep(merged, r"cg_wildcard\.wildcard_range\.signed_pattern.*' 2")
test.file_grep(merged, r"cg_four_state\.selected\.exact_x.*' 0")
test.file_grep(merged, r"cg_four_state\.selected\.exact_z.*' 0")
test.file_grep(merged, r"cg_narrow_wildcard\.signed_values\.negative.*' 4")
test.file_grep(merged, r"cg_narrow_wildcard\.unsigned_values\.positive.*' 4")
test.file_grep(merged, r"cg_excluded\.selected\.kept.*' 4")
test.file_grep(merged, r"cg_excluded_wildcard\.selected\.kept.*' 4")
test.file_grep(merged, r"cg_excluded_wide\.selected\.kept.*' 2")
test.file_grep(merged, r"cg_excluded_many\.selected\.kept.*' 2")
test.file_grep(merged, r"cg_transition_ignore\.selected\.kept.*' 2")
test.file_grep(merged, r"cg_registry\.selected\.off_diagonal.*' 2")
test.file_grep(merged, r"cg_registry\.selected\.auto_0_x_auto_0.*' 1")
test.file_grep(merged, r"cg_words\.partial\.boundary.*' 9")
test.file_grep(merged, r"cg_words\.partial\.either.*' 17")
test.file_grep(merged, r"cg_words\.partial\.values\[8\]_x_values\[7\].*' 1")
test.file_grep_not(merged, r'\.no_tuple\b|\.no_bins\b|\.absent\b|\.reversed\b|\.outside_domain\b')
test.file_grep_not(merged, r'\.removed(?:_|\b)|\.not_expanded\b')
test.file_grep_not(merged, r'\.pattern_miss\b')
test.file_grep_not(merged, r'\.unsigned_negative\b')

test.passes()
