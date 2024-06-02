// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Yutetsu TAKATSUKASA.
// SPDX-License-Identifier: CC0-1.0

`begin_keywords "VAMS-2.3"

module t (/*autoarg*/
   // Inputs
   clk
   );

   input clk;

   integer cyc = 0;

   real  vin[0:1] /*verilator split_var*/;
   wreal vout[0:1] /*verilator split_var*/;
   swap  i_swap(.in0(vin[0]), .in1(vin[1]), .out0(vout[0]), .out1(vout[1]));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==0) begin
        // Setup
         vin[0] = 1.0;
         vin[1] = 2.0;
      end
      else if (cyc==2) begin
         vin[0] = 3.0;
         vin[1] = 4.0;
      end
      else if (cyc==3) begin
         if (vout[0] == vin[1] && vout[1] == vin[0]) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end else begin
            $write("Mismatch %f %f\n", vout[0], vout[1]);
            $stop;
         end
      end
   end

endmodule

module swap
  (input wreal in0, in1,
   output wreal out0, out1);
   wreal tmp[0:1] /* verilator split_var*/;
   assign tmp[0] = in0;
   assign tmp[1] = in1;
   assign out0 = tmp[1];
   assign out1 = tmp[0];
endmodule
