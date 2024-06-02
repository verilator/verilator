// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// bug998

interface intf
  #(parameter PARAM = 0)
   ();

   int p1;
   generate
      initial p1 = 1;
   endgenerate

   int p2;
   generate begin
      initial p2 = 1;
   end
   endgenerate

   int p3;
   int p3_no;
   if (PARAM == 1) initial p3 = 1; else initial p3_no = 1;

   int p4;
   int p4_no;
   case (PARAM)
     1: initial p4 = 1;
     default: initial p4_no = 1;
   endcase

   int p5;
   for (genvar g=0; g<=PARAM; ++g) initial p5 = 1;

endinterface

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   intf #(.PARAM(1)) my_intf ();

   always @ (posedge clk) begin
      if (my_intf.p1 != 1) $stop;
      if (my_intf.p2 != 1) $stop;
      if (my_intf.p3 != 1) $stop;
      if (my_intf.p3_no != 0) $stop;
      if (my_intf.p4 != 1) $stop;
      if (my_intf.p4_no != 0) $stop;
      if (my_intf.p5 != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
