#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import shutil

import vltest_bootstrap

test.scenarios('vlt')

prog = os.environ["VERILATOR_ROOT"] + "/bin/verilator_trace_diff"


def write_text(filename, lines):
    with open(filename, 'w', encoding='utf8') as fh:
        fh.write("\n".join(lines) + "\n")


def write_vcd(filename, timescale, time_factor, data, msg, include_msg=True, include_real=True):
    lines = [
        "$timescale " + timescale + " $end",
        "$scope module top $end",
        "$var wire 1 ! clk $end",
        '$var wire 4 " data $end',
    ]
    if include_real:
        lines.append('$var real 1 # temp $end')
    if include_msg:
        lines.append('$var string 1 $ msg $end')
    lines.extend([
        "$upscope $end",
        "$enddefinitions $end",
        "$dumpvars",
        "0!",
        'b0000 "',
    ])
    if include_real:
        lines.append("r1.5 #")
    if include_msg:
        lines.append("sok $")
    lines.append("$end")
    for cycle in range(1, 11):
        lines.append("#" + str((cycle * 10 - 5) * time_factor))
        lines.append("1!")
        lines.append("#" + str(cycle * 10 * time_factor))
        lines.append("0!")
    lines.append("#" + str(100 * time_factor))
    lines.append('b' + data + ' "')
    if include_real:
        lines.append("r2.5 #")
    if include_msg:
        lines.append("s" + msg + " $")
    write_text(filename, lines)


def run_diff(extra_args, logfile, status):
    test.run(cmd=[prog] + extra_args + [">", logfile, "2>&1; echo $? >", status])
    return test.file_contents(status).strip()


trace1 = test.obj_dir + "/trace1.vcd"
trace2 = test.obj_dir + "/trace2.vcd"
data_log = test.obj_dir + "/data.log"
data_status = test.obj_dir + "/data.status"
same_log = test.obj_dir + "/same.log"
same_status = test.obj_dir + "/same.status"
string_log = test.obj_dir + "/string.log"
string_status = test.obj_dir + "/string.status"
missing_log = test.obj_dir + "/missing.log"
missing_status = test.obj_dir + "/missing.status"
fst_log = test.obj_dir + "/fst.log"
fst_status = test.obj_dir + "/fst.status"
array_log = test.obj_dir + "/array.log"
array_status = test.obj_dir + "/array.status"
dumpvars_log = test.obj_dir + "/dumpvars.log"
dumpvars_status = test.obj_dir + "/dumpvars.status"
dumpall_log = test.obj_dir + "/dumpall.log"
dumpall_status = test.obj_dir + "/dumpall.status"
real_log = test.obj_dir + "/real.log"
real_status = test.obj_dir + "/real.status"

write_vcd(trace1, '1ns', 1, '0111', 'bad')
write_vcd(trace2, '1ps', 1000, '0110', 'bad')

if run_diff(["--clock", "top.clk", trace1, trace2], data_log, data_status) != '1':
    test.error("Expected exit code 1 for a difference")
test.file_grep(
    data_log,
    r'^First difference at time 100 \(cycle 10\): top\.data \(trace1=0111, trace2=0110\)$')

write_vcd(trace1, '1ns', 1, '0111', 'bad')
write_vcd(trace2, '1ns', 1, '0111', 'bad')
if run_diff(["--clock", "top.clk", trace1, trace2], same_log, same_status) != '0':
    test.error("Expected exit code 0 for identical traces")

write_vcd(trace1, '1ns', 1, '0111', 'bad')
write_vcd(trace2, '1ns', 1, '0111', 'good')
if run_diff(["--clock", "top.clk", trace1, trace2], string_log, string_status) != '1':
    test.error("Expected exit code 1 for a string difference")
test.file_grep(
    string_log,
    r'^First difference at time 100 \(cycle 10\): top\.msg \(trace1=bad, trace2=good\)$')

write_vcd(trace1, '1ns', 1, '0111', 'bad')
write_vcd(trace2, '1ns', 1, '0111', 'bad', include_msg=False)
if run_diff([trace1, trace2], missing_log, missing_status) != '2':
    test.error("Expected exit code 2 for different signal sets")
test.file_grep(missing_log, r'Signal only in .*trace1\.vcd: top\.msg')

write_text(trace1, [
    "$timescale 1ns $end",
    "$scope module top $end",
    "$var wire 1 ! clk $end",
    '$var wire 1 " arr[0] $end',
    '$var wire 1 # arr[1] $end',
    "$upscope $end",
    "$enddefinitions $end",
    "$dumpvars",
    "0!",
    '0"',
    "0#",
    "$end",
    "#10",
    "1!",
])

write_text(trace2, [
    "$timescale 1ns $end",
    "$scope module top $end",
    "$var wire 1 ! clk $end",
    '$var wire 1 " arr[0] $end',
    '$var wire 1 # arr[1] $end',
    "$upscope $end",
    "$enddefinitions $end",
    "$dumpvars",
    "0!",
    '0"',
    "0#",
    "$end",
    "#10",
    "1!",
    '1"',
])

if run_diff(["--clock", "top.clk", trace1, trace2], array_log, array_status) != '1':
    test.error("Expected exit code 1 for an array element difference")
test.file_grep(array_log,
               r'^First difference at time 10 \(cycle 1\): top\.arr\[0\] \(trace1=0, trace2=1\)$')

write_text(trace1, [
    "$timescale 1ns $end",
    "$scope module top $end",
    "$var wire 1 ! clk $end",
    '$var wire 4 " data $end',
    "$upscope $end",
    "$enddefinitions $end",
    '$dumpvars 0! b1010 " $end',
])

write_text(trace2, [
    "$timescale 1ns $end",
    "$scope module top $end",
    "$var wire 1 ! clk $end",
    '$var wire 4 " data $end',
    "$upscope $end",
    "$enddefinitions $end",
    '$dumpvars 0! b1011 " $end',
])

if run_diff([trace1, trace2], dumpvars_log, dumpvars_status) != '1':
    test.error("Expected exit code 1 for values on a $dumpvars line")
test.file_grep(dumpvars_log,
               r'^First difference at time 0: top\.data \(trace1=1010, trace2=1011\)$')

write_text(trace1, [
    "$timescale 1ns $end",
    "$scope module top $end",
    "$var wire 1 ! clk $end",
    '$var wire 4 " data $end',
    "$upscope $end",
    "$enddefinitions $end",
    "$dumpvars",
    "0!",
    'b0000 "',
    "$end",
    "#10",
    '$dumpall 1! b1010 " $end',
])

write_text(trace2, [
    "$timescale 1ns $end",
    "$scope module top $end",
    "$var wire 1 ! clk $end",
    '$var wire 4 " data $end',
    "$upscope $end",
    "$enddefinitions $end",
    "$dumpvars",
    "0!",
    'b0000 "',
    "$end",
    "#10",
    '$dumpall 1! b1011 " $end',
])

if run_diff([trace1, trace2], dumpall_log, dumpall_status) != '1':
    test.error("Expected exit code 1 for values on a $dumpall line")
test.file_grep(dumpall_log,
               r'^First difference at time 10: top\.data \(trace1=1010, trace2=1011\)$')

write_text(trace1, [
    "$timescale 1ns $end",
    "$scope module top $end",
    "$var real 1 ! value $end",
    "$upscope $end",
    "$enddefinitions $end",
    "$dumpvars",
    "r1.50 !",
    "$end",
])

write_text(trace2, [
    "$timescale 1ns $end",
    "$scope module top $end",
    "$var real 1 ! value $end",
    "$upscope $end",
    "$enddefinitions $end",
    "$dumpvars",
    "r1.5 !",
    "$end",
])

if run_diff([trace1, trace2], real_log, real_status) != '0':
    test.error("Expected equal real values with different formatting to match")

if shutil.which('fst2vcd') and shutil.which('vcd2fst'):
    simple = test.obj_dir + "/simple.vcd"
    fst = test.obj_dir + "/trace.fst"
    write_vcd(simple, '1ns', 1, '0111', 'bad', include_msg=False, include_real=False)
    test.run(cmd=[shutil.which('vcd2fst'), simple, fst])
    if run_diff([simple, fst], fst_log, fst_status) != '0':
        test.error("Expected exit code 0 for an FST generated from the same VCD")
else:
    print("- FST smoke test skipped: install GTKWave with fst2vcd and vcd2fst")

test.passes()
