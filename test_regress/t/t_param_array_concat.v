// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jonathan Drolet
// SPDX-License-Identifier: CC0-1.0

// Overrides of unpacked array parameters by unpacked array concatenations

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef logic [31:0] arr_t[2];
typedef logic [31:0] arr2_t[2][2];

// Issue #6686
module sub #(
    parameter logic [31:0] MASK[2] = {32'h0007_FFFF, 32'h0000_FFFF},
    parameter logic [1:0] EXP_MATCH = 2'b11
);
  logic [1:0] match;
  for (genvar i = 0; i < 2; i++) begin : g
    assign match[i] = &(MASK[i][15:0]);
  end
  initial #1 `checkh(match, EXP_MATCH);
endmodule

module types #(
    parameter arr_t T = '{0, 0},
    parameter arr2_t D = '{default: 0},
    parameter logic [63:0] PK = 0,
    parameter logic [31:0] ONE[1] = '{0}
);
endmodule

module t;
  localparam logic [31:0] C_MASK_FSS = 32'h0007_FFFF;
  localparam logic [31:0] C_MASK_OTPSS = 32'h0000_FF0F;
  localparam arr_t ROW0 = '{1, 2};
  localparam arr_t ROW1 = '{3, 4};

  sub u_default ();
  sub #(
      .MASK({C_MASK_FSS, C_MASK_OTPSS}),
      .EXP_MATCH(2'b01)
  ) u_override ();

  // A typedef, an array of arrays concatenated from arrays, a packed parameter, and one item
  types #(
      .T({C_MASK_OTPSS, C_MASK_FSS}),
      .D({ROW1, ROW0}),
      .PK({C_MASK_FSS, C_MASK_OTPSS}),
      .ONE({C_MASK_FSS})
  ) u_types ();

  initial begin
    `checkh(u_override.MASK[0], 32'h0007_FFFF);
    `checkh(u_override.MASK[1], 32'h0000_FF0F);
    `checkh(u_types.T[0], 32'h0000_FF0F);
    `checkh(u_types.T[1], 32'h0007_FFFF);
    `checkd(u_types.D[0][1], 4);
    `checkd(u_types.D[1][0], 1);
    `checkh(u_types.PK, 64'h0007_FFFF_0000_FF0F);
    `checkh(u_types.ONE[0], 32'h0007_FFFF);
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
