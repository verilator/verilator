// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

//bug991
module t (/*AUTOARG*/);

   typedef struct {
      logic [31:0] arr [3:0];
   } a_t;

   typedef struct {
      logic [31:0] arr [0:3];
   } b_t;


   a_t array_assign;
   a_t array_other;

   b_t larray_assign;
   b_t larray_other;

   initial begin
      array_assign.arr[0] = 32'd1;
      array_assign.arr[3:1] = '{32'd4, 32'd3, 32'd2};

      array_other.arr[0] = array_assign.arr[0]+10;
      array_other.arr[3:1] = array_assign.arr[3:1];
      if (array_other.arr[0] != 11) $stop;
      if (array_other.arr[1] != 2) $stop;
      if (array_other.arr[2] != 3) $stop;
      if (array_other.arr[3] != 4) $stop;

      larray_assign.arr[0] = 32'd1;
      larray_assign.arr[1:3] = '{32'd4, 32'd3, 32'd2};

      larray_other.arr[0] = larray_assign.arr[0]+10;
      larray_other.arr[1:3] = larray_assign.arr[1:3];
      if (larray_other.arr[0] != 11) $stop;
      if (larray_other.arr[1] != 4) $stop;
      if (larray_other.arr[2] != 3) $stop;
      if (larray_other.arr[3] != 2) $stop;

      larray_other.arr = '{5, 6, 7, 8};
      if (larray_other.arr[0] != 5) $stop;
      if (larray_other.arr[1] != 6) $stop;
      if (larray_other.arr[2] != 7) $stop;
      if (larray_other.arr[3] != 8) $stop;

      larray_other.arr = larray_assign.arr;
      if (larray_other.arr[0] != 1) $stop;
      if (larray_other.arr[1] != 4) $stop;
      if (larray_other.arr[2] != 3) $stop;
      if (larray_other.arr[3] != 2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
