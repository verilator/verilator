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

test.scenarios('vlt_all', 'ms')

# The exclusion checks intentionally reference ignore/default bins.
test.ms_run_flags += ['-suppress', '13196']
test.compile(verilator_flags2=[
    '--coverage', '--debug-self-test', '--dump-tree', '--dump-tree-json', '--timing'
],
             ms_flags2=['-suppress', '13196'],
             timing_loop=True,
             threads=(2 if test.vltmt else 1))
test.execute()

if test.vlt_all:
    coverage_covergroup_common.covergroup_coverage_report(test)
    test.files_identical(test.obj_dir + '/covergroup_report.txt', test.golden_filename)

    tree_files = test.glob_some(test.obj_dir + '/*.tree')
    json_files = test.glob_some(test.obj_dir + '/*.tree.json')
    test.file_grep_any(tree_files, r'COVERBINSOF.*\[NEGATED\]')
    test.file_grep_any(tree_files, r'COVERCROSSSELECT.*\[AND\]')
    test.file_grep_any(tree_files, r'COVERCROSSSELECT.*\[OR\]')
    test.file_grep_any(json_files, r'"type":"COVERBINSOF".*"isNegated":true')
    test.file_grep_any(json_files, r'"type":"COVERCROSSSELECT".*"isOr":true')
    test.file_grep_any(json_files,
                       r'"type":"COVERCROSSDTYPE".*"dimensions":2.*"tuples":1.*"bins":10')

    headers = test.glob_some(test.obj_dir + '/' + test.vm_prefix + '*.h')
    test.file_grep_any(headers, r'VlCoverCrossT<2,\s*1,\s*10,\s*0,\s*10>')
    test.file_grep_any(headers, r'VlCoverCrossT<2,\s*0,\s*0,\s*0,\s*0>')
    test.file_grep_any(headers, r'VlCoverCrossT<2,\s*256,\s*2,\s*0,\s*5>')

    guards_cpp = test.glob_one(test.obj_dir + '/' + test.vm_prefix + '*cg_guards__Vclpkg__0.cpp')
    test.file_grep_not(guards_cpp, r'static_cast<bool>')

    merged = test.obj_dir + '/merged.dat'
    test.run(cmd=[
        os.environ['VERILATOR_ROOT'] + '/bin/verilator_coverage', '--write', merged,
        test.coverage_filename
    ],
             verilator_run=True)
    test.file_grep(merged, r"cg_sets\.logic_ops\.not_hit_negation.*' (\d+)", 8)
    test.file_grep(merged, r"cg_sets\.logic_ops\.named_not_hit.*' (\d+)", 16)
    test.file_grep(merged, r"cg_sets\.logic_ops\.named_not_miss.*' (\d+)", 20)
    test.file_grep(merged, r"cg_partial\.selected\.either_zero.*' (\d+)", 3)
    test.file_grep(merged, r"cg_partial\.selected\.auto_1_x_auto_1.*' (\d+)", 1)
    test.file_grep(merged, r"cg_precedence\.three_axes\.ungrouped.*' (\d+)", 5)
    test.file_grep(merged, r"cg_precedence\.three_axes\.grouped.*' (\d+)", 3)
    test.file_grep(merged, r"cg_precedence\.three_axes\.mixed.*' (\d+)", 4)
    test.file_grep(merged, r"cg_fast_paths\.selected\.early_a.*' (\d+)", 7)
    test.file_grep(merged, r"cg_fast_paths\.selected\.early_b.*' (\d+)", 7)
    test.file_grep(merged, r"cg_fast_paths\.selected\.late.*' (\d+)", 2)
    test.file_grep(merged, r"cg_fast_paths\.selected\.first_x_second_x_first.*' (\d+)", 7)
    test.file_grep(merged, r"cg_guards\.selected\.low_bit.*' (\d+)", 4)
    test.file_grep(merged, r"cg_guards\.selected\.high_bit.*' (\d+)", 4)
    test.file_grep(merged, r"cg_guards\.selected\.selected_bit.*' (\d+)", 3)
    test.file_grep(merged, r"cg_guards\.selected\.low_slice.*' (\d+)", 6)
    test.file_grep(merged, r"cg_guards\.selected\.whole_vector.*' (\d+)", 7)
    test.file_grep(merged, r"cg_guards\.selected\.wide_bit.*' (\d+)", 4)
    test.file_grep(merged, r"cg_guards\.selected\.wide_vector.*' (\d+)", 6)
    test.file_grep(merged, r"cg_guards\.selected\.signed_vector.*' (\d+)", 4)
    test.file_grep(merged, r"cg_guards\.selected\.constant_true.*' (\d+)", 8)
    test.file_grep(merged, r"cg_fixed_words\.selected\.all_values.*' (\d+)", 16)
    test.file_grep(merged, r"cg_fixed_words\.sparse\.all_values.*' (\d+)", 16)
    test.file_grep(merged, r"cg_fixed_words\.sparse\.subset.*' (\d+)", 4)
    test.file_grep(merged, r"cg_fixed_words\.guarded\.all_values.*' (\d+)", 16)
    test.file_grep(merged, r"cg_fixed_words\.guarded\.subset.*' (\d+)", 2)
    test.file_grep(merged, r"cg_guards\.selected\.unguarded.*' (\d+)", 8)
    test.file_grep(merged, r"cg_hit_words\.selected\.low.*' (\d+)", 3)
    test.file_grep(merged, r"cg_hit_words\.selected\.boundary.*' (\d+)", 2)
    test.file_grep(merged, r"cg_hit_words\.selected\.high.*' (\d+)", 4)
    test.file_grep(merged, r"cg_hit_words\.selected\.ends.*' (\d+)", 4)
    test.file_grep(merged, r"cg_hit_words\.selected\.b1_x_b0.*' (\d+)", 4)
    test.file_grep(merged, r"cg_hit_words\.selected\.b1_x_b1.*' (\d+)", 3)
    test.file_grep(merged, r"cg_hit_words\.whole\.all_values.*' (\d+)", 10)
    test.file_grep(merged, r"cg_hit_words\.single_guarded\.ends.*' (\d+)", 4)
    test.file_grep(merged, r"cg_hit_words\.single_guarded\.b7_x_b0.*' (\d+)", 4)
    test.file_grep(merged, r"cg_numeric\.numeric\.typed_negative.*' (\d+)", 2)
    test.file_grep(merged, r"cg_wildcard\.wildcard_range\.signed_pattern.*' (\d+)", 2)
    test.file_grep(merged, r"cg_four_state\.selected\.exact_x.*' (\d+)", 0)
    test.file_grep(merged, r"cg_four_state\.selected\.exact_z.*' (\d+)", 0)
    test.file_grep(merged, r"cg_narrow_wildcard\.signed_values\.negative.*' (\d+)", 4)
    test.file_grep(merged, r"cg_narrow_wildcard\.unsigned_values\.positive.*' (\d+)", 4)
    test.file_grep(merged, r"cg_excluded\.selected\.kept.*' (\d+)", 4)
    test.file_grep(merged, r"cg_excluded_wildcard\.selected\.kept.*' (\d+)", 4)
    test.file_grep(merged, r"cg_excluded_wide\.selected\.kept.*' (\d+)", 2)
    test.file_grep(merged, r"cg_excluded_many\.selected\.kept.*' (\d+)", 2)
    test.file_grep(merged, r"cg_transition_ignore\.selected\.kept.*' (\d+)", 2)
    test.file_grep(merged, r"cg_registry\.selected\.off_diagonal.*' (\d+)", 2)
    test.file_grep(merged, r"cg_registry\.selected\.auto_0_x_auto_0.*' (\d+)", 1)
    test.file_grep(merged, r"cg_words\.partial\.boundary.*' (\d+)", 9)
    test.file_grep(merged, r"cg_words\.partial\.either.*' (\d+)", 17)
    test.file_grep(merged, r"cg_words\.partial\.values\[8\]_x_values\[7\].*' (\d+)", 1)
    test.file_grep_not(merged,
                       r'\.no_tuple\b|\.no_bins\b|\.absent\b|\.reversed\b|\.outside_domain\b')
    test.file_grep_not(merged, r'\.removed(?:_|\b)|\.not_expanded\b')
    test.file_grep_not(merged, r'\.pattern_miss\b')
    test.file_grep_not(merged, r'\.unsigned_negative\b')

test.passes()
