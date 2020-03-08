// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc=1;
   integer c_trace_on;
   real    r;

   sub sub ();

   always @ (posedge clk) begin
      if (cyc != 0) begin
         r <= r + 0.1;
      end
   end
endmodule

module sub;
   integer inside_sub_a = 2;
endmodule
