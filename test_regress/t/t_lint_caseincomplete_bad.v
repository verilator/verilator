// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input [1:0] i
);

  always_comb begin
    case (i)
      2'b00: ;
      2'b10: ;
      2'b11: ;
    endcase

    unique0 case (i)  // No warning
      2'b00: ;
    endcase
  end

endmodule
