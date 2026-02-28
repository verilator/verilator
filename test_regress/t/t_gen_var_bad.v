// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2005 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   integer i;
   generate
      for (i=0; i<3; i=i+1) begin  // Bad: i is not a genvar
      end
   endgenerate
endmodule
