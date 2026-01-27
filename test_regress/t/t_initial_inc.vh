// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2003 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define foo bar
`ifdef foo
 `ifdef baz `else
// Test file to make sure includes work;
   integer user_loaded_value;
 `endif
`endif
