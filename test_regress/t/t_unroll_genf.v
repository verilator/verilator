// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

//bug830
module sub();
endmodule

function integer cdiv(input integer x);
   begin
      cdiv = 10;
   end
endfunction

module t (/*AUTOARG*/);

   genvar j;
   generate
      for (j = 0; j < cdiv(10); j=j+1)
        sub sub();
   endgenerate

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
