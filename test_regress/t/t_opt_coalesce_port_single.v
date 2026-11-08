// DESCRIPTION: Verilator: Keep the input of a single instance that needs an assignment
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct packed {
  logic [6:0] hi;
  logic [6:0] lo;
} pair_t;

module sub (
    input logic [6:0] i,
    input logic [6:0] k,
    output logic [6:0] o
);
  /*verilator no_inline_module*/
  assign o = (i * k) ^ 7'h53;
endmodule

module t;
  pair_t s;
  wire [6:0] x;
  // Connected to a constant, not a variable, so the port needs an assignment
  sub u (
      s.lo,
      7'd3,
      x
  );

  initial begin
    for (int k = 0; k < 32; ++k) begin
      s = {7'(5 * k), 7'(3 * k + 1)};
      #1;
      `checkh(x, (s.lo * 7'd3) ^ 7'h53);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
