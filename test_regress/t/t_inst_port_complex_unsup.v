// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// No simulator supporting this was found
module ansi_rename (
  input .ai_rename(ai),  .bi_rename(b),
  output wire .ao_rename(ao),  .bo_rename(bo)
);
  assign ao = ai;
  assign bo = bi;
endmodule

module nansi_rename (
  .ai_rename(ai), .bi_rename(bi),
  .ao_rename(ao), .bo_rename(bo)
);
  input ai;
  input bi;
  output ao;
  output bo;
  assign ao = ai;
  assign bo = bi;
endmodule

// No simulator supporting this was found
module ansi_split (
  input .ci_30(ci[3:0]), .ci_74(ci[7:4]),
  output wire .co_30(co[3:0]),  .co_74(co[7:4])
);
  assign co = ci;
endmodule

module nansi_split (
  ci[3:0], ci[7:4],
  co[3:0], co[7:4]
);
  input [7:0] ci;
  output [7:0] co;
  assign co = ci;
endmodule

module nansi_concat (
  {ai, bi},
  {ao, bo}
);
  input [1:0] ai, bi;
  output [1:0] ao, bo;
  assign ao = ai;
  assign bo = bi;
endmodule

module nansi_concat_named (
  .abi({ai, bi}),
  .abo({ao, bo})
);
  input [1:0] ai, bi;
  output [1:0] ao, bo;
  assign ao = ai;
  assign bo = bi;
endmodule

module nansi_same_input(aa, aa);
  input aa;
endmodule

// Some simulators don't support aggregated ports with different directions
module nansi_mixed_direction(.aio({ai, ao}));
  input ai;
  output ao;
endmodule

module t;
  // TODO make self checking
  initial $finish;
endmodule
