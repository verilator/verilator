// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

interface ifc
  #(
    parameter int unsigned WIDTH
    ) ();
   typedef struct {
     logic [WIDTH-1:0] data;
   } struct_t;
endinterface

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   ifc #(10) i_ifc10();
   ifc #(20) i_ifc20();

   sub #(10) u_sub10 (.clk, .ifc_if(i_ifc10));
   sub #(20) u_sub20 (.clk, .ifc_if(i_ifc20));

   integer cyc = 1;
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module sub #(
     parameter int EXP_WIDTH)
   (
    input logic clk,
    ifc ifc_if);
   typedef ifc_if.struct_t struct_t;

   wire [EXP_WIDTH-1:0] expval = '1;

   initial begin
      struct_t substruct;
      substruct.data = '1;
      `checkh(substruct.data, expval);
   end

endmodule
