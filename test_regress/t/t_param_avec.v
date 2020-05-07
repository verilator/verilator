// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2016 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   sub #(.IDX(0), .CHK(10)) i0;
   sub #(.IDX(2), .CHK(12)) i2;
   sub #(.IDX(7), .CHK(17)) i7;
   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module sub ();
   function integer get_element;
      input integer index;
      input integer array_arg[7:0];
      get_element = array_arg[index];
   endfunction

   parameter integer IDX = 5;
   parameter integer CHK = 5;
   localparam integer array[0:7] = '{10, 11, 12, 13, 14, 15, 16, 17};
   localparam element1 = array[IDX];
   localparam elementf = get_element(IDX, array);
   initial begin
      `checkh (element1, CHK);
      `checkh (elementf, CHK);
   end
endmodule
