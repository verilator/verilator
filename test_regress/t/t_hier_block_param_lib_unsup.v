// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  // Libraries are found by comparing parameter values, not types
  typedef logic [5:0] word_t;
  typed #(.T(logic signed [6:0])) t0 ();
  typed #(.T(word_t)) t1 ();
  typed2 #(
      .TIN(logic [3:0]),
      .TOUT(logic [7:0])
  ) t2 ();
  nonansi #(.T(logic [1:0])) t3 ();
  outer o0 ();
  // The generated child arguments cannot carry these strings
  localparam string S0 = "p/*q*/r";
  localparam string S1 = "p //q";
  localparam string S2 = "p\"q";
  localparam string S3 = "p\nq";
  str_blk #(.S(S0)) s0 ();
  str_blk #(.S(S1)) s1 ();
  str_blk #(.S(S2)) s2 ();
  str_blk #(.S(S3)) s3 ();
  // A library cannot receive defparams
  fixed f0 ();
  defparam f0.child.N = 2;
  nested n0 ();
  generated g0 ();
endmodule

module typed #(
    parameter type T = logic [6:0]
);
  /*verilator hier_block*/
  T x;
endmodule

module typed2 #(
    parameter type TIN = logic,
    parameter type TOUT = logic
);
  /*verilator hier_block*/
  TIN i;
  TOUT o;
endmodule

module nonansi;
  /*verilator hier_block*/
  parameter type T = logic;
  T x;
endmodule

// Sets a type parameter of the block inside it
module outer #(
    parameter type T = logic [4:0]
);
  /*verilator hier_block*/
  typed #(.T(T)) inner ();
endmodule

module str_blk #(
    parameter string S = "x"
);
  /*verilator hier_block*/
endmodule

module fixed;
  /*verilator hier_block*/
  leaf child ();
endmodule

// Defparam in a module below the block
module nested;
  /*verilator hier_block*/
  mid m ();
endmodule

module mid;
  leaf child ();
  defparam child.N = 3;
endmodule

// Defparam inside a generate construct
module generated;
  /*verilator hier_block*/
  if (1) begin : g
    leaf child ();
    defparam child.N = 4;
  end
endmodule

module leaf #(
    parameter int N = 7
);
endmodule
