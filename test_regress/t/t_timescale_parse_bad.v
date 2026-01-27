// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// units < precision
`timescale 1ps/1ns

// Bad scale
`timescale frump
`timescale 1xs
`timescale 2ps
`timescale 1ns / frump
`timescale 1ns / 1ps /extra

module t;
  timeunit 2ps;  // Bad
  timeprecision 2ps;   // Bad
endmodule
