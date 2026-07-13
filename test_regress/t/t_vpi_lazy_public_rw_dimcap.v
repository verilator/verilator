// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// 'wide' has 4 packed dims, one more than the VPI table's dv[] cap: must
// retain, not reconstruct. 'narrow' is ordinary and must still reconstruct.
module t (
  input logic clk,
  input logic rst,
  output logic [7:0] observe
);

  logic [7:0] ctr;
  logic [1:0][1:0][1:0][1:0] wide;
  logic [7:0] narrow;

  assign wide = {ctr, ~ctr};
  assign narrow = ctr + 8'h1;

  always_ff @(posedge clk) begin
    if (rst) begin
      ctr <= 8'h0;
      observe <= 8'h0;
    end else begin
      ctr <= ctr + 8'h3;
      observe <= narrow;
    end
  end

endmodule
