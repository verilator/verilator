// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk, d0, d1
   );

   input clk;
   input [7:0] d0, d1;

   logic [7:0] inia [1:0][3:0] = '{ '{ '0, '1, 8'hfe, 8'hed },
                                    '{ '1, '1, 8'h11, 8'h22 }};
   logic [7:0] inil [0:1][0:3] = '{ '{ '0, '1, 8'hfe, 8'hed },
                                    '{ '1, '1, 8'h11, 8'h22 }};

   logic [7:0] data [1:0][3:0];
   logic [7:0] datl [0:1][0:3];

   initial begin
      data = '{ '{ d0, d1, 8'hfe, 8'hed },
                '{ d1, d1, 8'h11, 8'h22 }};
      data[0] = '{ d0, d1, 8'h19, 8'h39 };

      datl = '{ '{ d0, d1, 8'hfe, 8'hed },
                '{ d1, d1, 8'h11, 8'h22 }};
      datl[0] = '{ d0, d1, 8'h19, 8'h39 };

`ifdef TEST_VERBOSE
      $display("D=%x %x %x %x -> 39 19 x x", data[0][0], data[0][1], data[0][2], data[0][3]);
      $display("D=%x %x %x %x -> ed fe x x", data[1][0], data[1][1], data[1][2], data[1][3]);
      $display("L=%x %x %x %x -> x x 19 39", datl[0][0], datl[0][1], datl[0][2], datl[0][3]);
      $display("L=%x %x %x %x -> x x 11 12", datl[1][0], datl[1][1], datl[1][2], datl[1][3]);
`endif
      if (inia[0][0] !== 8'h22) $stop;
      if (inia[0][1] !== 8'h11) $stop;
      if (inia[1][0] !== 8'hed) $stop;
      if (inia[1][1] !== 8'hfe) $stop;

      if (inil[0][2] !== 8'hfe) $stop;
      if (inil[0][3] !== 8'hed) $stop;
      if (inil[1][2] !== 8'h11) $stop;
      if (inil[1][3] !== 8'h22) $stop;

      if (data[0][0] !== 8'h39) $stop;
      if (data[0][1] !== 8'h19) $stop;
      if (data[1][0] !== 8'hed) $stop;
      if (data[1][1] !== 8'hfe) $stop;

      if (datl[0][2] !== 8'h19) $stop;
      if (datl[0][3] !== 8'h39) $stop;
      if (datl[1][2] !== 8'h11) $stop;
      if (datl[1][3] !== 8'h22) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
