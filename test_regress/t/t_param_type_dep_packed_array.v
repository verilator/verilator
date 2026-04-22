// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Packed 2D type param with dependent dims.  Both dims must resolve
// per-spec.

module m #(
    parameter int  W = 4,
    parameter int  D = 2,
    parameter type T = logic [D-1:0][W-1:0]
) ();
  T val;
  initial val = '1;
endmodule

module t;
  m #(.W(4), .D(2)) i_a ();
  m #(.W(8), .D(3)) i_b ();
  m #(.W(2), .D(4)) i_c ();

  initial begin
    #1;
    if ($bits(i_a.val) !== 8) begin
      $write("%%Error $bits(i_a.val)=%0d\n", $bits(i_a.val)); $stop;
    end
    if ($bits(i_a.val[0]) !== 4) begin
      $write("%%Error $bits(i_a.val[0])=%0d\n", $bits(i_a.val[0])); $stop;
    end
    if (i_a.val[0] !== 4'hF) begin $write("%%Error i_a.val[0]=%h\n", i_a.val[0]); $stop; end
    if (i_a.val[1] !== 4'hF) begin $write("%%Error i_a.val[1]=%h\n", i_a.val[1]); $stop; end

    if ($bits(i_b.val) !== 24) begin
      $write("%%Error $bits(i_b.val)=%0d\n", $bits(i_b.val)); $stop;
    end
    if ($bits(i_b.val[0]) !== 8) begin
      $write("%%Error $bits(i_b.val[0])=%0d\n", $bits(i_b.val[0])); $stop;
    end
    if (i_b.val[0] !== 8'hFF) begin $write("%%Error i_b.val[0]=%h\n", i_b.val[0]); $stop; end
    if (i_b.val[1] !== 8'hFF) begin $write("%%Error i_b.val[1]=%h\n", i_b.val[1]); $stop; end
    if (i_b.val[2] !== 8'hFF) begin $write("%%Error i_b.val[2]=%h\n", i_b.val[2]); $stop; end

    if ($bits(i_c.val) !== 8) begin
      $write("%%Error $bits(i_c.val)=%0d\n", $bits(i_c.val)); $stop;
    end
    if ($bits(i_c.val[0]) !== 2) begin
      $write("%%Error $bits(i_c.val[0])=%0d\n", $bits(i_c.val[0])); $stop;
    end
    if (i_c.val[0] !== 2'h3) begin $write("%%Error i_c.val[0]=%h\n", i_c.val[0]); $stop; end
    if (i_c.val[3] !== 2'h3) begin $write("%%Error i_c.val[3]=%h\n", i_c.val[3]); $stop; end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
