// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
//     Recursive type definition via circular parameter type defaults
//     should produce a clear error with type chain display.

// Circular: A defaults to B, B defaults to A
module circ #(
    parameter type A = B,
    parameter type B = A
) (
    input A ai,
    output B bo
);
  assign bo = ai;
endmodule

module t ();
  logic [7:0] x, y;
  circ u_circ (
      .ai(x),
      .bo(y)
  );
  initial begin
    $finish;
  end
endmodule
