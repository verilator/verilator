// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Andrew Bardsley.
// SPDX-License-Identifier: CC0-1.0

// bug1071

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [3:0] array_1 [2:0];
   reg [3:0] array_2 [2:0];
   reg [3:0] array_3 [3:1];

   reg [3:0] elem;

   reg array_1_ne_array_2;
   reg array_1_eq_array_2;
   reg array_1_ne_array_3;
   reg array_1_eq_array_3;

   initial begin
      array_1[0] = 4'b1000;
      array_1[1] = 4'b1000;
      array_1[2] = 4'b1000;

      array_2[0] = 4'b1000;
      array_2[1] = 4'b1000;
      array_2[2] = 4'b1000;

      array_3[1] = 4'b1000;
      array_3[2] = 4'b0100;
      array_3[3] = 4'b0100;

      array_1_ne_array_2 = array_1 != array_2;  // 0
      array_1_eq_array_2 = array_1 == array_2;  // 0
      array_1_ne_array_3 = array_1 != array_3;  // 1
      array_1_eq_array_3 = array_1 == array_3;  // 1

      //Not legal: array_rxor  = ^ array_1;
      //Not legal: array_rxnor = ^~ array_1;
      //Not legal: array_ror   = | array_1;
      //Not legal: array_rand  = & array_1;

`ifdef TEST_VERBOSE
      $write("array_1_ne_array2==%0d\n", array_1_ne_array_2);
      $write("array_1_ne_array3==%0d\n", array_1_ne_array_3);
`endif

      if (array_1_ne_array_2 !== 0) $stop;
      if (array_1_eq_array_2 !== 1) $stop;
      if (array_1_ne_array_3 !== 1) $stop;
      if (array_1_eq_array_3 !== 0) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
