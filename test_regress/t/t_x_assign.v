// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2020 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t_x_assign(
   input wire clk,
   output reg o
);
   always @(posedge clk) begin
      if (1'bx) o <= 1'd1; else o <= 1'd0;
   end
endmodule
