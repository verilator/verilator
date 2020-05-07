// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   parameter int SIZES [3:1] = '{10,20,30};
   parameter int SUMS3 = SIZES[3];
   parameter int SUMS2 = SIZES[2];
   parameter int SUMS1 = SIZES[1];

   parameter int LE_SIZES [1:3] = '{10,20,30};
   parameter int LE_SUMS3 = LE_SIZES[3];
   parameter int LE_SUMS2 = LE_SIZES[2];
   parameter int LE_SUMS1 = LE_SIZES[1];

   function int from_array(int index);
      if (index != 0); return SIZES[index];
   endfunction
   function int from_array_le(int index);
      if (index != 0); return LE_SIZES[index];
   endfunction

   initial begin
      if (SUMS1 != 30) $stop;
      if (SUMS2 != 20) $stop;
      if (SUMS3 != 10) $stop;
      if (LE_SUMS1 != 10) $stop;
      if (LE_SUMS2 != 20) $stop;
      if (LE_SUMS3 != 30) $stop;
      if (from_array(1) != 30) $stop;
      if (from_array(2) != 20) $stop;
      if (from_array(3) != 10) $stop;
      if (from_array_le(1) != 10) $stop;
      if (from_array_le(2) != 20) $stop;
      if (from_array_le(3) != 30) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
