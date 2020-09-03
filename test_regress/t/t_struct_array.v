// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package TEST_TYPES;
   typedef struct packed {
      logic 	  stuff;
   } a_struct_t;
endpackage // TEST_TYPES

module t(clk);
   input clk;
   TEST_TYPES::a_struct_t [3:0] a_out;
   sub sub (.a_out);
   always @ (posedge clk) begin
      if (a_out[0] != 1'b0) $stop;
      if (a_out[1] != 1'b1) $stop;
      if (a_out[2] != 1'b0) $stop;
      if (a_out[3] != 1'b1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module sub(a_out);
   parameter n = 4;
   output TEST_TYPES::a_struct_t [n-1:0] a_out;
   always_comb begin
      for (int i=0;i<n;i++)
	a_out[i].stuff = i[0];
   end
endmodule

// Local Variables:
// verilog-typedef-regexp: "_t$"
// End:
