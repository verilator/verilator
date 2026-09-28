#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

import re
import shutil

test.scenarios('vltmt')
test.top_filename = "t/t_hier_block_perf.v"
cycles = 100
test.sim_time = cycles * 10 + 1000

threads = 2
config_file = test.t_dir + "/" + test.name + ".vlt"
flags = [config_file, "--hierarchical", "-Wno-UNOPTFLAT", "-DSIM_CYCLES=" + str(cycles)]

test.compile(v_flags2=["--prof-pgo"] + flags, threads=threads)


def check_interface(name, ports, combo, seq, ignore):
    filename = test.obj_dir + '/V' + name + '/' + name + '.sv'
    declarations = [(r'module ' + name + r'\s*\((.*?)\);', ports)]
    for suffix, args in (('combo_update', combo), ('seq_update', seq), ('combo_ignore', ignore)):
        declarations.append((r'function \w+ ' + name + '_protectlib_' + suffix + r'\((.*?)\);',
                             ['handle__V'] + args))
    for pattern, expected in declarations:
        match = test.file_grep(filename, '(?s)' + pattern)
        if match:
            actual = [port.split()[-1] for port in match[0].split(',')]
            if actual != expected:
                test.error('Exported interface order differs: ' + name + ': ' + str(actual))


def check_interfaces():
    # These modules have no generated ports; all source ports retain their order.
    check_interface('Test', ['rdata', 'rdata2', 'clk', 'we', 'sel', 'wdata'],
                    ['rdata', 'rdata2', 'we', 'sel', 'wdata'], ['rdata', 'rdata2', 'clk'],
                    ['we', 'sel', 'wdata'])
    check_interface('Check', ['clk', 'crc', 'result', 'rdata', 'rdata2'],
                    ['crc', 'result', 'rdata', 'rdata2'], ['clk', 'crc'],
                    ['result', 'rdata', 'rdata2'])
    check_interface('CoreHier', ['clk'], [], ['clk'], [])

test.execute(all_run_flags=[
    "+verilator+prof+exec+start+0",
    " +verilator+prof+exec+file+/dev/null",
    " +verilator+prof+vlt+file+" + test.obj_dir + "/profile.vlt"])  # yapf:disable

test.file_grep(test.obj_dir + "/profile.vlt", r'profile_data -model "VTest"')
test.file_grep(test.obj_dir + "/profile.vlt", r'profile_data -model "VCheck"')
test.file_grep(test.obj_dir + "/profile.vlt", r'profile_data -model "VCoreHier"')
test.file_grep(test.obj_dir + "/profile.vlt", r'profile_data -model "V' + test.name + '"')

# Check for cost rollovers
test.file_grep_not(test.obj_dir + "/profile.vlt", r'.*cost 64\'d\d{18}.*')

# Replace measured task costs with reproducible unequal costs, so the layout
# exercised by this check does not depend on the host's timing measurements.
profile = test.file_contents(test.obj_dir + '/profile.vlt')
pattern = r'(profile_data -model "[^"]+" -mtask "[^"]+" -cost 64\'d)\d+'
keys = sorted(set(re.findall(pattern, profile)))
costs = {key: str((index + 1)**2) for index, key in enumerate(keys)}
with open(test.obj_dir + '/layout_profile.vlt', 'w', encoding='utf8') as fh:
    fh.write(re.sub(pattern, lambda match: match[1] + costs[match[1]], profile))

# PGO must preserve the exported DPI interface even when field layout changes.
wrappers = [
    test.obj_dir + '/' + name
    for name in ('VTest/Test.sv', 'VCheck/Check.sv', 'VCoreHier/CoreHier.sv')
]
for filename in wrappers:
    shutil.copyfile(filename, filename + '.before_pgo')
layout_file = test.obj_dir + '/VTest/VTest___024root.h'
layout_pattern = r'\bVL_(?:IN|OUT)\w*\((\w+),'
layout_before = re.findall(layout_pattern, test.file_contents(layout_file))

# Differentiate results
test.name = test.name + "_optimized"
test.compile(
    # Intentionally no --prof-pgo here to make sure profile data can be read in
    # without it (that is: --prof-pgo has no effect on profile_data hash names)
    v_flags2=[test.obj_dir + "/layout_profile.vlt"] + flags,
    threads=threads)

test.execute()

for filename in wrappers:
    test.files_identical(filename, filename + '.before_pgo')

# Read directly: file_contents caches by name, but this header was rebuilt.
with open(layout_file, encoding='utf8') as fh:
    if re.findall(layout_pattern, fh.read()) == layout_before:
        test.error('PGO fixture did not change the child port field order')
check_interfaces()

test.passes()
