// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nick Brereton
// SPDX-License-Identifier: CC0-1.0

module leaf #(
    parameter int V = 0
);
endmodule

module mid #(
    parameter int R = 1
);
  if (R == 1) begin : g
    leaf u ();
  end
  else begin : g
    int u;
  end
  defparam g.u.V = 5;
endmodule

module t;
  mid u_m ();
endmodule
