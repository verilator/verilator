// DESCRIPTION: Verilator: Verilog Test module
//
// Negative test for the struct-localparam field-access folding in V3Param
// (resolveDotToTypedef).  Malformed outer `.field` chains on a class
// localparam value must produce clean user-facing errors, NOT an internal
// error or a crash in the following width pass.  Exercises the three
// mismatch guards in the field-chain walk:
//   (1) outer Dot rhs is not a plain field identifier (bit-select)
//   (2) `.field` applied to a non-struct value
//   (3) field name not a member of the struct
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
  logic [7:0] cam_type;
  logic [7:0] depth;
} inner_t;

typedef struct packed {
  inner_t     jt;
  logic [7:0] tag;
} cfg_t;

class C #(parameter int W = 1);
  localparam cfg_t cfg = '{jt: '{cam_type: W[7:0], depth: W[7:0] + 8'd1},
                           tag: W[7:0] + 8'd2};
endclass

module Sub #(parameter int WIDTH = 0) ();
endmodule

module Mid #(parameter int W = 8) ();
  typedef C#(W) CFG;
  // (1) bit-select after the field chain: outer Dot rhs is not a ParseRef
  Sub #(int'(CFG::cfg.jt.cam_type[0])) u_fieldref ();
  // (2) `.bogus` on the scalar field `tag`: dotting into a non-struct
  Sub #(int'(CFG::cfg.tag.bogus)) u_nonstruct ();
  // (3) `.nosuchfield` not a member of struct `jt`
  Sub #(int'(CFG::cfg.jt.nosuchfield)) u_nomember ();
endmodule

module t;
  Mid #(.W(8)) u ();
endmodule
