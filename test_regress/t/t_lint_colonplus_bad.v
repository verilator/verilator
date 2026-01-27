// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2017 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   z
   );

   reg [3:0] r = 4'b1010;
   output [2:1] z = r[2 :+ 1];

endmodule
