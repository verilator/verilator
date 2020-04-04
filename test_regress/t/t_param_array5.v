// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

//bug1578
module t;
   parameter N = 4;

   typedef logic array_t[N];

   parameter array_t MASK = mask_array();
   //TODO bug1578: parameter MASK = mask_array();

   function array_t mask_array();
      for(int i = 0; i < N; i++) begin
         mask_array[i] = i[0];
      end
   endfunction

   array_t norm;

   initial begin
      if (N != 4) $stop;
      norm = mask_array();
      if (norm[0] != 1'b0) $stop;
      if (norm[1] != 1'b1) $stop;
      if (norm[2] != 1'b0) $stop;
      if (norm[3] != 1'b1) $stop;
      if (MASK[0] != 1'b0) $stop;
      if (MASK[1] != 1'b1) $stop;
      if (MASK[2] != 1'b0) $stop;
      if (MASK[3] != 1'b1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
