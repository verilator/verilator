// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t
  (
   input wire clk
   );

   integer    cyc; initial cyc = 0;
   integer    unchanged; initial unchanged = 42;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
   end
endmodule
