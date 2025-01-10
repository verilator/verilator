// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Very simple test for interface pathclearing

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc=1;

   ifc #(1) itopa();
   ifc #(2) itopb();

   sub #(1) ca (.isub(itopa),
                .i_value(4));
   sub #(2) cb (.isub(itopb),
                .i_value(5));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==1) begin
         if (itopa.MODE != 1) $stop;
         if (itopb.MODE != 2) $stop;
      end
      if (cyc==20) begin
         if (itopa.get_value() != 4) $stop;
         if (itopb.get_value() != 5) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module sub
  #(parameter MODE = 0)
   (
   ifc.out_modport isub,
   input integer i_value
   );

   always @* isub.value = i_value;

endmodule

interface ifc;
   parameter MODE = 0;
   // Modports under generates not supported by all commercial simulators

   integer value;
   modport out_modport (output value);
   function integer get_value(); return value; endfunction

   // IEEE 1800-2017 deprecated alowing modports inside generates
   // generate if (MODE == 0) begin
   //    integer valuea;
   //    modport out_modport (output valuea);
   //    function integer get_valuea(); return valuea; endfunction
   // end
endinterface
