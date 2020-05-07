// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package pkg;
   typedef enum bit [1:0]
   {
    E__NOT   = 2'b00,
    E__VAL   = 2'b11
    } E_t;
endpackage

module t;
   reg [1:0]  ttype;
   reg        m;

   enum       bit [1:0] { LOCAL } l;

   always @ (m or 1'b0 or LOCAL) begin
      // Don't complain about constants in sensitivity lists
   end

   initial begin
      ttype = pkg::E__NOT;
      m = (ttype == pkg::E__VAL);
      if (m != 1'b0) $stop;

      ttype = pkg::E__VAL;
      m = (ttype == pkg::E__VAL);
      if (m != 1'b1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
