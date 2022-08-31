// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2022 by Wilson Snyder.

module flop (q, d, clk);
   // No AUTOARG; order of below is different from port order above
   input wire clk;
   output reg q;
   input wire d;

   // verilator hier_block

   always_ff @(posedge clk) begin
     q <= d;
   end

endmodule

module t (
          output wire q,
          input wire  d,
          input wire  clk
          );

   // This intentionally uses pin number ordering
   flop u_flop(q, d, clk);

endmodule
