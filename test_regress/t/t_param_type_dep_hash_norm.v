// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Hash-normalization: the port type must resolve per-specialization, not
// from the template default.  Two pin values differing only in bits above
// the template-default width must still produce distinct specs when the
// actual spec's width is wider.  Pin values equal after widthing must
// share a spec (#5479 dedup preserved).

module test #(
    parameter int width = 16,
    parameter int width2 = width + 8,
    parameter type data_t = logic [width2-1:0],
    parameter data_t data = data_t'(0)
) ();
endmodule

module t;
  // width=24 -> width2=32 -> data_t is 32 bits
  test #(.width(24), .data(32'hFFFFFFFF)) i_aa ();
  test #(.width(24), .data(32'h11FFFFFF)) i_ab ();
  test #(.width(24), .data(32'h11FFFFFF)) i_ac ();
  // width=16 -> width2=24 -> data_t is 24 bits
  test #(.width(16), .data(24'hFFFFFF)) i_bb ();

  initial begin
    if ($bits(i_aa.data) !== 32) begin
      $write("%%Error $bits(i_aa.data)=%0d expected 32\n", $bits(i_aa.data)); $stop;
    end
    if ($bits(i_ab.data) !== 32) begin
      $write("%%Error $bits(i_ab.data)=%0d expected 32\n", $bits(i_ab.data)); $stop;
    end
    if ($bits(i_ac.data) !== 32) begin
      $write("%%Error $bits(i_ac.data)=%0d expected 32\n", $bits(i_ac.data)); $stop;
    end
    if ($bits(i_bb.data) !== 24) begin
      $write("%%Error $bits(i_bb.data)=%0d expected 24\n", $bits(i_bb.data)); $stop;
    end
    if (i_aa.data !== 32'hFFFFFFFF) begin
      $write("%%Error i_aa.data=%h\n", i_aa.data); $stop;
    end
    if (i_ab.data !== 32'h11FFFFFF) begin
      $write("%%Error i_ab.data=%h\n", i_ab.data); $stop;
    end
    if (i_ac.data !== 32'h11FFFFFF) begin
      $write("%%Error i_ac.data=%h\n", i_ac.data); $stop;
    end
    if (i_bb.data !== 24'hFFFFFF) begin
      $write("%%Error i_bb.data=%h\n", i_bb.data); $stop;
    end
    // Distinct full-32b values must NOT share a spec (values differ).
    if (i_aa.data === i_ab.data) begin
      $write("%%Error i_aa.data and i_ab.data must differ\n"); $stop;
    end
    // Equal pin values share a spec (#5479 dedup).
    if (i_ab.data !== i_ac.data) begin
      $write("%%Error i_ab.data and i_ac.data must match\n"); $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
