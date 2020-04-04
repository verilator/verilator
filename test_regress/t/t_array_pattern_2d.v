// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

//bug991
module t (/*AUTOARG*/);

   logic [31:0] array_assign [3:0];
   logic [31:0] array_other [3:0];

   logic [31:0] larray_assign [0:3];
   logic [31:0] larray_other [0:3];

   initial begin
      array_assign[0] = 32'd1;
      array_assign[3:1] = '{32'd4, 32'd3, 32'd2};

      array_other[0] = array_assign[0]+10;
      array_other[3:1] = array_assign[3:1];
      if (array_other[0] != 11) $stop;
      if (array_other[1] != 2) $stop;
      if (array_other[2] != 3) $stop;
      if (array_other[3] != 4) $stop;

      larray_assign[0] = 32'd1;
      larray_assign[1:3] = '{32'd4, 32'd3, 32'd2};

      larray_other[0] = larray_assign[0]+10;
      larray_other[1:3] = larray_assign[1:3];
      if (larray_other[0] != 11) $stop;
      if (larray_other[1] != 4) $stop;
      if (larray_other[2] != 3) $stop;
      if (larray_other[3] != 2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
