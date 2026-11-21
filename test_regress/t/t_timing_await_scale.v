// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  parameter int Size = 100;

  // Each process awaits the edge of its own bit
  logic [Size-1:0] c = '0;
  int rises[Size];
  int ownRises[Size];
  for (genvar i = 0; i < Size; ++i) begin : g
    initial forever begin
      @(posedge c[i]);
      ++rises[i];
    end
    // Another process makes the edge of the bit, then awaits it
    initial begin
      #1 c[i] = 1;
      @(posedge c[i]);
      ++ownRises[i];
    end
  end

  // Sensitive to the other edge of a bit awaited above
  int falls = 0;
  always @(negedge c[0]) ++falls;
endmodule
