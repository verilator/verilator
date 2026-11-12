// DESCRIPTION: Verilator: An always_latch with nonblocking assignments runs at time zero
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  // Open from the start, with inputs that never change
  logic en = 1;
  logic [3:0] dreg = 4'h9;
  wire [3:0] dw = dreg;
  logic [3:0] l_var, l_wire;
  always_latch if (en) l_var <= dreg;
  always_latch if (en) l_wire <= dw;

  always @(posedge clk) begin
    `checkh(l_var, 4'h9);
    `checkh(l_wire, 4'h9);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
