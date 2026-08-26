// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t #(parameter int SIZE = 4);

  // verilator lint_off UNDRIVEN
  // verilator lint_off UNUSEDSIGNAL

  reg i;
  wire I;

  import pkg::*;

  // Parameters and localparams are elaborated away, so they must not
  // collide with a net that differs only in lexical case
  localparam int WIDTH = 8;
  logic [WIDTH-1:0] width;
  logic [WIDTH-1:0] reg_ctrl;
  logic [SIZE-1:0] size;

  initial begin
    width = WIDTH[WIDTH-1:0];
    reg_ctrl = REG_CTRL;
    size = {SIZE{1'b0}};
    if (width !== 8'd8) $stop;
    if (reg_ctrl !== 8'h00) $stop;
    if (size !== {SIZE{1'b0}}) $stop;
    $finish;
  end

endmodule

package pkg;
  localparam logic [7:0] REG_CTRL = 8'h00;
endpackage
