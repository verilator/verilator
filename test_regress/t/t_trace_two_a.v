// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc=1;
   integer c_trace_on;

   sub sub ();

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         c_trace_on <= cyc + 2;
         if (cyc==10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

module sub;
   integer inside_sub_a = 1;
endmodule
