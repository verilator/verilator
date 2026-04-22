// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Dedup preservation: three instances with identical override values
// should simulate identically.  #5479's equality-collapse property must
// not be broken by the fall-through fix.

module m #(
    parameter int  W   = 8,
    parameter type T   = logic [W-1:0],
    parameter T    VAL = '0
) ();
  logic [W-1:0] observed;
  assign observed = VAL;
endmodule

module t;
  m #(.W(16), .VAL(16'hBEEF)) i1 ();
  m #(.W(16), .VAL(16'hBEEF)) i2 ();
  m #(.W(16), .VAL(16'hBEEF)) i3 ();

  initial begin
    #1;
    if ($bits(i1.observed) !== 16) begin $write("%%Error i1 bits\n"); $stop; end
    if ($bits(i2.observed) !== 16) begin $write("%%Error i2 bits\n"); $stop; end
    if ($bits(i3.observed) !== 16) begin $write("%%Error i3 bits\n"); $stop; end
    if (i1.observed !== 16'hBEEF) begin $write("%%Error i1=%h\n", i1.observed); $stop; end
    if (i2.observed !== 16'hBEEF) begin $write("%%Error i2=%h\n", i2.observed); $stop; end
    if (i3.observed !== 16'hBEEF) begin $write("%%Error i3=%h\n", i3.observed); $stop; end
    if (i1.observed !== i2.observed) begin $write("%%Error i1!=i2\n"); $stop; end
    if (i2.observed !== i3.observed) begin $write("%%Error i2!=i3\n"); $stop; end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
