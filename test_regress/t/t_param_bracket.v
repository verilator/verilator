// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder;
// SPDX-License-Identifier: CC0-1.0

module t
  #(parameter WIDTH = 8)
   (/*AUTOARG*/
   // Outputs
   o
   );
   output [WIDTH-1:0] o;
   localparam DEPTH = $clog2(5);
   // Note single bracket below
   reg [WIDTH-1:0] arid [1<<DEPTH];
   assign o = arid[0];
endmodule
