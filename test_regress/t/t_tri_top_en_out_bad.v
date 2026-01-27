// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Paul Wright
// SPDX-License-Identifier: CC0-1.0
//
// A submodule to ensure that __en and __out propagate upwards
// This version of the test should fail
`define T_TRI_TOP_NAME t_tri_top_en_out_bad
`define SKIP_TIMING 1
`include "t_tri_top_en_out.v"
