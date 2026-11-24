// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module sub #(
    parameter int DYN[] = '{1},
    parameter int QUE[$] = '{2},
    parameter int ASC[string] = '{"a": 3},
    parameter int WLD[*] = '{1: 4}
);
endmodule

module t;
  int v = 1;

  // Non-constant localparam elements
  localparam int L_DYN[] = '{1, v};
  localparam int L_QUE[$] = '{2, v};
  localparam int L_ASC[string] = '{"a": v};
  localparam int L_WLD[*] = '{1: v};

  // Non-constant override elements
  sub #(
      .DYN('{1, v}),
      .QUE('{2, v}),
      .ASC('{"a": v}),
      .WLD('{1: v})
  ) elem ();

  // Non-constant override values
  int dv[] = '{1};
  int qv[$] = '{2};
  int av[string] = '{"a": 3};
  int wv[*] = '{1: 4};
  sub #(
      .DYN(dv),
      .QUE(qv),
      .ASC(av),
      .WLD(wv)
  ) whole ();

  // Selects from parameters
  localparam int C_DYN[] = '{1, 2};
  localparam int C_DYN_1 = C_DYN[1];
  localparam int C_QUE[$] = '{1, 2};
  localparam int C_QUE_1 = C_QUE[1];
  localparam int C_ASC[string] = '{"a": 1};
  localparam int C_ASC_A = C_ASC["a"];
  localparam int C_WLD[*] = '{1: 2};
  localparam int C_WLD_1 = C_WLD[1];
endmodule
