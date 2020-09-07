// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   logic [31:0] array_assign [3:0];

   logic [31:0] larray_assign [0:3];

   logic [31:0] array_assign2 [6:3];

   logic [31:0] larray_assign2 [3:6];
   initial begin
      array_assign[1:3] = '{32'd4, 32'd3, 32'd2};
      larray_assign[3:1] = '{32'd4, 32'd3, 32'd2};
      array_assign2[4:6] = '{32'd4, 32'd3, 32'd2};
      larray_assign2[6:4] = '{32'd4, 32'd3, 32'd2};

      array_assign[4:3] = '{32'd4, 32'd3};
      array_assign[1:-1] = '{32'd4, 32'd3};
      array_assign[1:1] = '{32'd4};  // Ok
      larray_assign[1:1] = '{32'd4};  // Ok
      array_assign2[4:4] = '{32'd4};  // Ok
      larray_assign2[4:4] = '{32'd4};  // Ok

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
