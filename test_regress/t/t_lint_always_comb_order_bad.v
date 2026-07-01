// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Zhi QU
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] c,
    input logic sel,
    output logic [3:0] result1,
    output logic [3:0] result2,
    output logic [3:0] result3,
    output logic [3:0] y
);

  logic [3:0] accum1;
  logic [3:0] accum2;
  logic [3:0] accum3;

  always_comb begin
    result1 = a + accum1;
    accum1 = b;
  end

  always_comb begin
    accum2 = b;
    result2 = a + accum2;  // write-before-read: do not warn
  end

  always_comb begin
    y = '0;
    if (sel) y = a;
    else y = b;
  end

  always_comb begin
    if (sel) begin
      result3 = a + accum3;
    end
    else begin
      result3 = c;
    end
    accum3 = b;
  end

endmodule
