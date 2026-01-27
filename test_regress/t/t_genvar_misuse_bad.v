// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
// See bug408

module top (
    output logic [1:0] q,
    input  logic [1:0] d,
    input  logic       clk
  );

  genvar i;
  assign q[i] = d[i];  // <--- Error: Misusing genvar i
  genvar a, b, c;
  for (a = 0; a < 2; ++a) begin
    if (a);
    for (b = 0; b < 2; ++b) begin
      if (a);
      if (b);
      if (c);  // <--- Error: Misusing genvar c
    end
  end

endmodule
