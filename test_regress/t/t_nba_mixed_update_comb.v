// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define check(got ,exp) do if ((got) !== (exp)) begin $write("%%Error: %s:%0d: cyc=%0d got='h%x exp='h%x\n", `__FILE__,`__LINE__, cyc, (got), (exp)); `stop; end while(0)

module t (/*AUTOARG*/
   // Inputs
   clk
   );
  input clk;


  reg [31:0] cyc = 0;
  reg [31:0] sameAsCycButCantBeOptimized;

  // 'x' has both blocking and non-blocking update, with the blocking
  // update in **combinational** logic
  reg [1:0] x = 2'b00;
  // '{y1, y0}' should have exactly the same value as 'x', at all times
  reg y0 = 1'b0;
  reg y1 = 1'b0;

  assign x[0] = cyc[0];
  assign y0 = sameAsCycButCantBeOptimized[0];

  always @(posedge clk) begin
     $display("cyc = %d (%08x) x[1] = %0d, x[0] = %0d, y1 = %0d, y0 = %0d", cyc, cyc, x[1], x[0], y1, y0);
     `check(y0, cyc[0]);
     `check(y1, cyc[0]);
     `check(x[0], cyc[0]);
     `check(x[1], cyc[0]);
     x[1] <= ~x[1];
     y1 <= ~y1;
     cyc = cyc + 1;
     sameAsCycButCantBeOptimized = cyc;
     if (cyc == 99) begin
       $display(x);
       $write("*-* All Finished *-*\n");
       $finish;
     end
  end

endmodule
