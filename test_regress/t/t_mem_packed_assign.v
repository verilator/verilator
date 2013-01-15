// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   /* verilator lint_off WIDTH */

   input clk;

   integer cyc; initial cyc = 0;
   logic [31:0] arr_c; initial arr_c = 0;
   logic [7:0] [3:0] arr;

   logic [31:0] arr2_c; initial arr2_c = 0;
   logic [7:0] [3:0] arr2;
   assign arr2_c = arr2;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      arr_c <= arr_c + 1;
      arr2 <= arr2 + 1;
`ifdef TEST_VERBOSE
      $write("cyc%0d c:%0x a0:%0x a1:%0x a2:%0x a3:%0x\n", cyc, arr_c, arr[0], arr[1], arr[2], arr[3]);
`endif
      if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

   /* verilator lint_on WIDTH */

endmodule
