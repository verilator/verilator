// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%p exp=%p\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t (
    input clk
);
  // First clock changes every input before cycle zero is sampled.
  reg [3:0] cyc = 15;
  wire [1:0] a = cyc[1:0];
  wire signed [1:0] s = cyc[1:0];
  wire signed b = cyc[2];
  wire [2:0] wide = cyc[2:0];
  wire signed [2:0] wide_s = cyc[2:0];
  reg [23:0] hit;
  reg [7:0] seen[24];
  wire generate_hit;

  // Width mismatches are intentional: IEEE 1800-2017 12.5 uses the maximum
  // width and an unsigned comparison if any expression or item is unsigned.
  // verilator lint_off WIDTHEXPAND
  // Generate case uses the same common unsigned type: 1'sb1 becomes 01.
  case (2'b01)
    1'sb1: assign generate_hit = 1'b1;
    default:
    assign generate_hit = 1'b0;
  endcase

  always @* begin
    // Original reproducer, then its runtime-variable counterpart.
    case (a)
      1'sb1: hit[0] = 1'b1;
      default: hit[0] = 1'b0;
    endcase
    case (a)
      b: hit[1] = 1'b1;
      default: hit[1] = 1'b0;
    endcase
    casez (a)
      1'sb1: hit[2] = 1'b1;
      default: hit[2] = 1'b0;
    endcase
    casez (a)
      b: hit[3] = 1'b1;
      default: hit[3] = 1'b0;
    endcase
    // verilator lint_off CASEX
    casex (a)
      1'sb1: hit[4] = 1'b1;
      default: hit[4] = 1'b0;
    endcase
    casex (a)
      b: hit[5] = 1'b1;
      default: hit[5] = 1'b0;
    endcase
    // verilator lint_on CASEX

    // Controls: unsigned item, explicit cast, and all-signed comparisons.
    case (a)
      1'b1: hit[6] = 1'b1;
      default: hit[6] = 1'b0;
    endcase
    case (s)
      $unsigned(1'sb1): hit[7] = 1'b1;
      default: hit[7] = 1'b0;
    endcase
    case (s)
      1'sb1: hit[8] = 1'b1;
      default: hit[8] = 1'b0;
    endcase
    case (s)
      b: hit[9] = 1'b1;
      default: hit[9] = 1'b0;
    endcase
    case (s)
      1'b1: hit[10] = 1'b1;
      default: hit[10] = 1'b0;
    endcase
    case ($signed(
        a
    ))
      1'sb1: hit[11] = 1'b1;
      default: hit[11] = 1'b0;
    endcase

    // A wider item must also propagate its type back to the expression.
    case (b)
      2'b01: hit[12] = 1'b1;
      default: hit[12] = 1'b0;
    endcase
    case (b)
      s: hit[13] = 1'b1;
      default: hit[13] = 1'b0;
    endcase
    case (cyc[2])
      s: hit[14] = 1'b1;
      default: hit[14] = 1'b0;
    endcase
    case (cyc[2])
      a: hit[15] = 1'b1;
      default: hit[15] = 1'b0;
    endcase

    // An unsigned item affects even a different, signed item in the case.
    case (s)
      1'sb1: hit[16] = 1'b1;
      2'b10: hit[16] = 1'b0;
      default: hit[16] = 1'b0;
    endcase
    casez (wide)
      2'sb1?: hit[17] = 1'b1;
      default: hit[17] = 1'b0;
    endcase
    // verilator lint_off CASEX
    casex (wide)
      2'sb1x: hit[18] = 1'b1;
      default: hit[18] = 1'b0;
    endcase
    // verilator lint_on CASEX
    casez (wide_s)
      2'sb1?: hit[19] = 1'b1;
      default: hit[19] = 1'b0;
    endcase
`ifndef IVERILOG
    // 12.5.4 uses inside comparisons; keep the integral extension controls.
    case (a) inside
      1'sb1: hit[20] = 1'b1;
      default: hit[20] = 1'b0;
    endcase
    case (s) inside
      1'sb1: hit[21] = 1'b1;
      default: hit[21] = 1'b0;
    endcase
`else
    // Icarus does not support case inside.
    hit[21:20] = 2'b00;
`endif
    unique case (a)
      1'sb1: hit[22] = 1'b1;
      default: hit[22] = 1'b0;
    endcase
    priority case (a)
      1'sb1: hit[23] = 1'b1;
      default: hit[23] = 1'b0;
    endcase
  end
  // verilator lint_on WIDTHEXPAND

  always @(posedge clk) begin
    cyc <= cyc + 1'b1;
    if (cyc < 8) begin
      for (int i = 0; i < 24; ++i) seen[i][cyc[2:0]] <= hit[i];
    end
    else if (cyc == 8) begin
      // Bit n records cycle n: a/s = 00,01,10,11 twice; b = 0 then 1.
      // Unsigned comparisons zero-extend 1'sb1 to 01: cycles 1 and 5.
      `checkh(seen[0], 8'b00100010);
      // b zero-extends to 00 then 01: cycles 0 and 5.
      `checkh(seen[1], 8'b00100001);
      // 12.5.1 gives casez/casex the same extension rules.
      `checkh(seen[2], 8'b00100010);
      `checkh(seen[3], 8'b00100001);
      `checkh(seen[4], 8'b00100010);
      `checkh(seen[5], 8'b00100001);
      // Unsigned item or $unsigned also gives 01: cycles 1 and 5.
      `checkh(seen[6], 8'b00100010);
      `checkh(seen[7], 8'b00100010);
      // All signed: 1'sb1 sign-extends to 11, and b to 00 then 11.
      `checkh(seen[8], 8'b10001000);
      `checkh(seen[9], 8'b10000001);
      // A signed expression with an unsigned item still compares as unsigned.
      `checkh(seen[10], 8'b00100010);
      // $signed(a) and the signed item give 11: cycles 3 and 7.
      `checkh(seen[11], 8'b10001000);
      // Wider unsigned item zero-extends b to 01: cycles 4 through 7.
      `checkh(seen[12], 8'b11110000);
      // Wider signed s sign-extends b to 00 then 11: cycles 0 and 7.
      `checkh(seen[13], 8'b10000001);
      // Unsigned expression or unsigned wider item gives 00 then 01.
      `checkh(seen[14], 8'b00100001);
      `checkh(seen[15], 8'b00100001);
      // The other unsigned item makes 1'sb1 become 01, even with signed s.
      `checkh(seen[16], 8'b00100010);
      // 1? / 1x zero-extend to 01? / 01x: only wide = 010 or 011.
      `checkh(seen[17], 8'b00001100);
      `checkh(seen[18], 8'b00001100);
      // All signed: 1? sign-extends to 11?, matching 110 and 111.
      `checkh(seen[19], 8'b11000000);
`ifndef IVERILOG
      // Integral inside comparisons likewise give 01 unsigned, 11 signed.
      `checkh(seen[20], 8'b00100010);
      `checkh(seen[21], 8'b10001000);
`endif
      // 12.5.3 qualifiers preserve unsigned extension to 01.
      `checkh(seen[22], 8'b00100010);
      `checkh(seen[23], 8'b00100010);
      `checkh(generate_hit, 1'b1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
