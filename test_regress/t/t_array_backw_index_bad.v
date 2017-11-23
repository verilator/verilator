// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Wilson Snyder.

module t (/*AUTOARG*/);

   logic [31:0] array_assign [3:0];

   logic [31:0] larray_assign [0:3];

   initial begin
      array_assign[1:3] = '{32'd4, 32'd3, 32'd2};
      larray_assign[3:1] = '{32'd4, 32'd3, 32'd2};

      array_assign[4:3] = '{32'd4, 32'd3};
      array_assign[1:-1] = '{32'd4, 32'd3};

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
