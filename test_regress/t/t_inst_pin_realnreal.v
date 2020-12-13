// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Peter Monsson.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   wire    gain = 1'b0;
   real    in;
   always_comb in = (cyc-4) * 1.0;
   wire    cmp;

   adc_netlist netlist(.clk, .in, .gain, .cmp);

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         $display("cyc=%0d cmp=%d", cyc, cmp);
         if (cyc == 3) begin
            if (cmp != 0) $stop;
         end
         else if (cyc == 4) begin
            if (cmp != 1) $stop;
         end
         else if (cyc == 5) begin
            if (cmp != 0) $stop;
         end
         else if (cyc == 10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

module adc_netlist(clk, in, gain, cmp);
   input clk;
   input real in;
   input gain;
   output cmp;

   wire pga_out; //TODO: convert to real or support real
   pga_model pga0(.in, .gain, .out(pga_out));
   comparator_model cmp0(.clk, .in(pga_out), .cmp);

endmodule

module pga_model(in, gain, out);
   input real in;
   input gain;
   output real out;

   always_comb begin
      out = in * 3.0;
   end

endmodule

module comparator_model(clk, in, cmp);
   input clk;
   input real in;
   output logic cmp;

   always_ff @(posedge clk) begin
      cmp <= in > 0.0;
   end

endmodule
