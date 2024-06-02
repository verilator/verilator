// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003-2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   reg [7:0] cyc; initial cyc = 0;

   reg [31:0] in;
   wire [31:0] out;
   t_extend_class_v sub (.in(in), .out(out));

   always @ (posedge clk) begin
      cyc <= cyc + 8'd1;
      if (cyc == 8'd1) begin
         in <= 32'h10;
      end
      if (cyc == 8'd2) begin
         if (out != 32'h11) $stop;
      end
      if (cyc == 8'd9) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module t_extend_class_v (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   in
   );

   input [31:0]  in;
   output logic [31:0] out;

   always @* begin
      // When "in" changes, call my method
      out = $c("this->m_myobjp->my_math(", in, ")");
   end

 `systemc_header
#include "t_extend_class_c.h"   // Header for contained object
 `systemc_interface
   t_extend_class_c* m_myobjp;  // Pointer to object we are embedding
 `systemc_ctor
   m_myobjp = new t_extend_class_c();   // Construct contained object
 `systemc_dtor
   delete m_myobjp;     // Destruct contained object
 `verilog

endmodule
