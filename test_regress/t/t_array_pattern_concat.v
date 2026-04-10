// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Greg Davill
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,
               expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

package arr_pkg;
  localparam logic [31:0] PKG_ADDRS[3] = '{32'hAA001000, 32'hAA002000, 32'hAA003000};
endpackage

module t (  /*AUTOARG*/);

  // Test: array concatenation in pattern initialization
  // An array localparam used as a value in another array's pattern
  // should have its elements "flattened" into the target array.

  localparam logic [31:0] BASE_ADDRS[3] = '{32'h80001000, 32'h80002000, 32'h80003000};

  // Sub-array slice at the start
  localparam logic [31:0] ALL_ADDRS[4] = '{BASE_ADDRS[0:1], 32'h80003000, 32'h80004000};

  // Sub-array slice in the middle
  localparam logic [31:0] MID[5] = '{32'hFF, BASE_ADDRS[0:1], 32'hAA, 32'hBB};

  // Multiple full sub-arrays
  localparam logic [31:0] EXTRA[2] = '{32'hC0, 32'hD0};
  localparam logic [31:0] MULTI[5] = '{BASE_ADDRS, EXTRA};

  // Sub-array with default (sparse InitArray)
  localparam logic [31:0] DFLT[3] = '{default: 32'hDD};
  localparam logic [31:0] WITH_DFLT[4] = '{DFLT, 32'hEE};

  // Slice at the end
  localparam logic [31:0] TAIL[4] = '{32'hAA, 32'hBB, BASE_ADDRS[1:2]};

  // Multiple slices combined
  localparam logic [31:0] MULTI_SLICE[4] = '{BASE_ADDRS[0:1], BASE_ADDRS[1:2]};

  // Single-element slice
  localparam logic [31:0] SINGLE[3] = '{BASE_ADDRS[0:0], 32'hAA, 32'hBB};

  // Descending-range source array
  localparam logic [31:0] DESC[2:0] = '{32'hD0, 32'hD1, 32'hD2};
  localparam logic [31:0] WITH_DESC[4] = '{DESC[1:0], 32'hAA, 32'hBB};

  // Slice bounds from parameter expressions
  localparam int unsigned N = 2;
  localparam logic [31:0] PARAM_SLICE[4] = '{BASE_ADDRS[0:N-1], 32'hAA, 32'hBB};

  // Multiple param-bounded slices composing a larger array
  localparam logic [31:0] SRC_A[4] = '{32'hA0, 32'hA1, 32'hA2, 32'hA3};
  localparam logic [31:0] SRC_B[4] = '{32'hB0, 32'hB1, 32'hB2, 32'hB3};
  localparam int unsigned NA = 2;
  localparam int unsigned NB = 3;
  localparam int unsigned TOTAL = NA + NB;
  localparam logic [31:0] COMPOSED[TOTAL] = '{SRC_A[0:NA-1], SRC_B[0:NB-1]};

  // Test key'd associative array initialisations
  localparam logic [31:0] KEY_ARR_A[4] = '{0: BASE_ADDRS[0:1], 2: 32'hF2, 3: 32'hF3};
  localparam logic [31:0] KEY_ARR_B[4] = '{2: ALL_ADDRS[1:2], default: 32'h00};

  // Keyed pattern where values are indexed from another array param —
  // the key determines position, not the source array's element count.
  localparam logic [31:0] KEYED_FROM_ARR[3] = '{
    0: BASE_ADDRS[2], 1: BASE_ADDRS[0], 2: BASE_ADDRS[1]
  };

  // Package-scoped array as a positional pattern member
  localparam logic [31:0] WITH_PKG[4] = '{arr_pkg::PKG_ADDRS, 32'hFF};

  // Package-scoped array slice
  localparam logic [31:0] PKG_SLICE[4] = '{arr_pkg::PKG_ADDRS[0:1], 32'hAA, 32'hBB};

  initial begin
    `checkh(ALL_ADDRS[0], 32'h80001000);
    `checkh(ALL_ADDRS[1], 32'h80002000);
    `checkh(ALL_ADDRS[2], 32'h80003000);
    `checkh(ALL_ADDRS[3], 32'h80004000);

    `checkh(MID[0], 32'hFF);
    `checkh(MID[1], 32'h80001000);
    `checkh(MID[2], 32'h80002000);
    `checkh(MID[3], 32'hAA);
    `checkh(MID[4], 32'hBB);

    `checkh(MULTI[0], 32'h80001000);
    `checkh(MULTI[1], 32'h80002000);
    `checkh(MULTI[2], 32'h80003000);
    `checkh(MULTI[3], 32'hC0);
    `checkh(MULTI[4], 32'hD0);

    `checkh(WITH_DFLT[0], 32'hDD);
    `checkh(WITH_DFLT[1], 32'hDD);
    `checkh(WITH_DFLT[2], 32'hDD);
    `checkh(WITH_DFLT[3], 32'hEE);

    `checkh(TAIL[0], 32'hAA);
    `checkh(TAIL[1], 32'hBB);
    `checkh(TAIL[2], 32'h80002000);
    `checkh(TAIL[3], 32'h80003000);

    `checkh(MULTI_SLICE[0], 32'h80001000);
    `checkh(MULTI_SLICE[1], 32'h80002000);
    `checkh(MULTI_SLICE[2], 32'h80002000);
    `checkh(MULTI_SLICE[3], 32'h80003000);

    `checkh(SINGLE[0], 32'h80001000);
    `checkh(SINGLE[1], 32'hAA);
    `checkh(SINGLE[2], 32'hBB);

    `checkh(WITH_DESC[0], 32'hD2);
    `checkh(WITH_DESC[1], 32'hD1);
    `checkh(WITH_DESC[2], 32'hAA);
    `checkh(WITH_DESC[3], 32'hBB);

    `checkh(PARAM_SLICE[0], 32'h80001000);
    `checkh(PARAM_SLICE[1], 32'h80002000);
    `checkh(PARAM_SLICE[2], 32'hAA);
    `checkh(PARAM_SLICE[3], 32'hBB);

    `checkh(COMPOSED[0], 32'hA0);
    `checkh(COMPOSED[1], 32'hA1);
    `checkh(COMPOSED[2], 32'hB0);
    `checkh(COMPOSED[3], 32'hB1);
    `checkh(COMPOSED[4], 32'hB2);

    `checkh(KEY_ARR_A[0], 32'h80001000);
    `checkh(KEY_ARR_A[1], 32'h80002000);
    `checkh(KEY_ARR_A[2], 32'hF2);
    `checkh(KEY_ARR_A[3], 32'hF3);

    `checkh(KEY_ARR_B[0], 32'h00);
    `checkh(KEY_ARR_B[1], 32'h00);
    `checkh(KEY_ARR_B[2], 32'h80002000);
    `checkh(KEY_ARR_B[3], 32'h80003000);

    `checkh(KEYED_FROM_ARR[0], 32'h80003000);
    `checkh(KEYED_FROM_ARR[1], 32'h80001000);
    `checkh(KEYED_FROM_ARR[2], 32'h80002000);

    `checkh(WITH_PKG[0], 32'hAA001000);
    `checkh(WITH_PKG[1], 32'hAA002000);
    `checkh(WITH_PKG[2], 32'hAA003000);
    `checkh(WITH_PKG[3], 32'hFF);

    `checkh(PKG_SLICE[0], 32'hAA001000);
    `checkh(PKG_SLICE[1], 32'hAA002000);
    `checkh(PKG_SLICE[2], 32'hAA);
    `checkh(PKG_SLICE[3], 32'hBB);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
