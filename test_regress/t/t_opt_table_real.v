// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Arthur Rosa
// SPDX-License-Identifier: CC0-1.0

module t (
    // Inputs
    clk
);
  input clk;

  reg [2:0] cyc;
  real x;
  shortreal xs;

  initial cyc = 0;
  always @(posedge clk) cyc <= cyc + 1;

  always @(cyc) begin
    case (cyc)
      3'd0: x = 1.0;
      3'd1: x = 2.0;
      3'd2: x = 3.0;
      3'd4: x = 5.0;
      3'd5: x = 6.0;
      default: x = 0.0;
    endcase
  end

  always @(cyc) begin
    case (cyc)
      3'd0: xs = 1.0;
      3'd1: xs = 2.0;
      3'd2: xs = 3.0;
      3'd4: xs = 5.0;
      3'd5: xs = 6.0;
      default: xs = 0.0;
    endcase
  end

  always @(posedge clk) begin
    if (xs != shortreal'(x)) $stop;
    $display("cyle %d = %.1f", cyc, x);
    if (cyc == 7) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
;
