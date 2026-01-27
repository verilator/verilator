// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Alias width check error test.
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  wire [1:0] a;
  wire [2:0] b;

  alias a = b;

endmodule
