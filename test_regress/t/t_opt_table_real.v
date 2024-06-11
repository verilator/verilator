// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024.
// SPDX-License-Identifier: CC0-1.0

module t (
    // Inputs
    clk
);
  input clk;

  reg [2:0] cyc;
  real x;

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

  always @(posedge clk) begin
    $display("cyle %d = %.1f", cyc, x);
    if (cyc == 7) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
;
