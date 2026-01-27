// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2010 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   bl, cl, bc, cc,
   // Inputs
   a
   );

   input logic a;
   output logic bl;
   output logic cl;
   always_latch begin
      bl <= a;  // No warning
      cl = a;
   end

   output logic bc;
   output logic cc;
   always_comb begin
      bc <= a;  // Warning
      cc = a;
   end


endmodule
