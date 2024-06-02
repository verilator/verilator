// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Very simple test for interface pathclearing

`ifdef VCS
 `define UNSUPPORTED_MOD_IN_GENS
`endif
`ifdef VERILATOR
 `define UNSUPPORTED_MOD_IN_GENS
`endif

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

`ifdef UNSUPPORTED_MOD_IN_GENS
   always @* isub.value = i_value;
`else
   generate if (MODE == 1) begin
      always @* isub.valuea = i_value;
   end
   else if (MODE == 2) begin
      always @* isub.valueb = i_value;
   end
   endgenerate
`endif

endmodule

interface ifc;
   parameter MODE = 0;
   // Modports under generates not supported by all commercial simulators
`ifdef UNSUPPORTED_MOD_IN_GENS
   integer value;
   modport out_modport (output value);
   function integer get_value(); return value; endfunction
`else
   generate if (MODE == 0) begin
      integer valuea;
      modport out_modport (output valuea);
      function integer get_valuea(); return valuea; endfunction
   end
   else begin
      integer valueb;
      modport out_modport (output valueb);
      function integer get_valueb(); return valueb; endfunction
   end
   endgenerate
`endif
endinterface
