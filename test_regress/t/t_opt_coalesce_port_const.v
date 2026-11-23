// DESCRIPTION: Verilator: Fold a constant input that is the same in every instance
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub (
    input logic [6:0] i,
    input logic [6:0] k,
    input logic [6:0] id,
    output logic [6:0] o
);
  /*verilator no_inline_module*/
  assign o = ((i * k) ^ 7'h53) + id;
endmodule

module t;
  logic [6:0] a, b;
  wire [6:0] x, y;
  // The same constant in both instances, through a wire: folded into the instances
  wire [6:0] three = 7'd3;
  // A different constant in each instance: kept, so the instances still share code
  sub u0 (
      a,
      three,
      7'd1,
      x
  );
  sub u1 (
      b,
      three,
      7'd2,
      y
  );

  initial begin
    for (int n = 0; n < 32; ++n) begin
      a = 7'(3 * n + 1);
      b = 7'(5 * n + 2);
      #1;
      `checkh(x, ((a * 7'd3) ^ 7'h53) + 7'd1);
      `checkh(y, ((b * 7'd3) ^ 7'h53) + 7'd2);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
