// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module mul (
    input [8:0] A,
    input [16:0] B,
    output [25:0] Y
);
  assign Y = $signed(A) * $signed(B);
endmodule

module A;
  wire [26:0] C;
  wire [26:0] D;
  wire [8:0] E;

  // This yields a circular DFG with a fairly special form that used to trip
  // decomposition.
  mul mul (
      .A(9'd10),
      .B(17'h0cccd),
      .Y({C[26], C[9:0], D[15:1]})
  );

  assign E = {C[8:0]};
  assign C[25:10] = {16{C[26]}};

endmodule
