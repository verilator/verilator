// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Chandan Egbert
// SPDX-License-Identifier: CC0-1.0

module sub();
endmodule

module t(input logic a, input logic b,
         output logic x, output logic y);

   always_comb begin
      integer i;
      x = a;
   end

   sub u0();

   always_comb begin
      integer j;
      y = b;
   end

endmodule
