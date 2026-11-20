// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

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
    // The edge made just before awaiting wakes only the process above
    initial begin
      #1 c[i] = 1;
      @(posedge c[i]);
      ++ownRises[i];
    end
  end

  // Sensitive to the other edge of a bit awaited above
  int falls = 0;
  always @(negedge c[0]) ++falls;

  initial begin
    #2 c = '0;
    #1 for (int i = 0; i < Size; ++i) c[i] = i % 3 == 0;
    #1;
    for (int i = 0; i < Size; ++i) begin
      `checkd(rises[i], i % 3 == 0 ? 2 : 1);
      `checkd(ownRises[i], i % 3 == 0 ? 1 : 0);
    end
    `checkd(falls, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
