// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub #(
  parameter int X = 1
) ();

  localparam int Y = X;
  localparam int Z = X;

endmodule

module t;
  localparam int MY_X = 2;

  sub #(.X(MY_X)) u_sub ();

  localparam int SUB_Y = u_sub.Y;  // <--- BAD: IEEE 1800-2023 6.20.2 no hierarchical

  initial begin
    `checkd(SUB_Y, 1);
    `checkd(u_sub.X, 2);
    `checkd(u_sub.Y, 1);
    `checkd(u_sub.Z, 2);
    $finish;
  end

endmodule
