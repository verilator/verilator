// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Interleaved specs (A B A C B A).  Any cross-instance leakage from
// template poisoning causes a later instance of a repeated tuple to
// mismatch its expected value.

module m #(
    parameter int  W   = 8,
    parameter type T   = logic [W-1:0],
    parameter T    VAL = '0
) ();
  logic [W-1:0] observed;
  assign observed = VAL;
endmodule

module t;
  m #(.W(8),  .VAL(8'h11))        ia1 ();  // A
  m #(.W(16), .VAL(16'h2222))     ib1 ();  // B
  m #(.W(8),  .VAL(8'h11))        ia2 ();  // A
  m #(.W(32), .VAL(32'h33333333)) ic1 ();  // C
  m #(.W(16), .VAL(16'h2222))     ib2 ();  // B
  m #(.W(8),  .VAL(8'h11))        ia3 ();  // A

  initial begin
    #1;
    if ($bits(ia1.observed) !== 8)  begin $write("%%Error ia1 bits\n"); $stop; end
    if ($bits(ib1.observed) !== 16) begin $write("%%Error ib1 bits\n"); $stop; end
    if ($bits(ia2.observed) !== 8)  begin $write("%%Error ia2 bits\n"); $stop; end
    if ($bits(ic1.observed) !== 32) begin $write("%%Error ic1 bits\n"); $stop; end
    if ($bits(ib2.observed) !== 16) begin $write("%%Error ib2 bits\n"); $stop; end
    if ($bits(ia3.observed) !== 8)  begin $write("%%Error ia3 bits\n"); $stop; end

    if (ia1.observed !== 8'h11)        begin $write("%%Error ia1=%h\n", ia1.observed); $stop; end
    if (ib1.observed !== 16'h2222)     begin $write("%%Error ib1=%h\n", ib1.observed); $stop; end
    if (ia2.observed !== 8'h11)        begin $write("%%Error ia2=%h\n", ia2.observed); $stop; end
    if (ic1.observed !== 32'h33333333) begin $write("%%Error ic1=%h\n", ic1.observed); $stop; end
    if (ib2.observed !== 16'h2222)     begin $write("%%Error ib2=%h\n", ib2.observed); $stop; end
    if (ia3.observed !== 8'h11)        begin $write("%%Error ia3=%h\n", ia3.observed); $stop; end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
