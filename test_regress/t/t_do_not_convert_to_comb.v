// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module t (
    clk,
    input wire i,
    output reg o_0,
    output reg o_1,
    output reg o_2,
    output reg o_3,
    output reg o_4,
    output reg o_5
   );

    input clk;

    reg a = 0;
    reg b = 0;

    event e;

    // We must not convert these blocks into combinational blocks

    always @(i) begin
      a <= ~a;
      o_0 = i;
    end

    always @(i) begin
      force b = 1;
      o_1 = i;
    end

    always @(i) begin
      release b;
      o_2 = i;
    end

    always @(i) begin
      -> e;
      o_3 = i;
    end

    always @(i) begin
      ->> e;
      o_4 = i;
    end

    always @(i) begin
      $display("Hello");
      o_5 = i;
    end

endmodule
