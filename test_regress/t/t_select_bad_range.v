// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2003 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  reg [43:0] mi;
  reg sel;
  reg [3:0] sel2;
  reg [3:0][3:0] packed_i;
  typedef logic [3:0][3:0] packed_t;
  packed_t packed_typedef;
  reg [3:0] packed_sel;
  reg [0:0][3:0] packed_slice;
  reg [3:0][3:0] packed_slice4;
  localparam integer PACKED_BAD_INDEX = 4;
  reg [3:0][0:0] packed_single;
  reg packed_bit;
  reg [5:2][6:0] packed_nonzero;
  /* verilator lint_off ASCRANGE */
  reg [1:3][6:0] packed_ascending;
  /* verilator lint_on ASCRANGE */
  reg [6:0] packed_sel7;

  always @(posedge clk) begin
    mi = 44'h123;
    sel = mi[44];
    sel2 = mi[44:41];
    packed_i = 16'h1234;
    packed_typedef = packed_i;
    // Out of range in the outer packed dimension.
    packed_sel = packed_i[4];
    packed_sel = packed_i[-1];
    packed_sel = packed_typedef[4];
    packed_sel = packed_i[PACKED_BAD_INDEX];
    packed_sel = packed_i[2+2];
    packed_slice = packed_i[4:4];
    packed_slice = packed_i[4+:1];
    packed_slice = packed_i[4-:1];
    packed_slice4 = packed_i[4:1];
    packed_sel = packed_i[3];  // Legal upper bound
    packed_sel = packed_i[0];  // Legal lower bound
    packed_slice = packed_i[3:3];
    packed_slice = packed_i[0+:1];
    packed_slice = packed_i[0-:1];
    packed_single = '0;
    packed_bit = packed_single[4];
    packed_bit = packed_single[-1];
    packed_nonzero = '0;
    // Below and above the declared [5:2] range.
    packed_sel7 = packed_nonzero[1];
    packed_sel7 = packed_nonzero[6];
    packed_sel7 = packed_nonzero[2];
    packed_ascending = '0;
    // Below and above the declared [1:3] range.
    packed_sel7 = packed_ascending[0];
    packed_sel7 = packed_ascending[4];
    packed_sel7 = packed_ascending[3];
    $write("Bad select %x %x\n", sel, sel2);
  end

  initial begin
    logic [-1:-2][3:0] packed_negative;
    packed_negative = '0;
    $write("Legal negative selects %x %x\n", packed_negative[-1], packed_negative[-2]);
  end
endmodule
