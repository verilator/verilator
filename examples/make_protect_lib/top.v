// DESCRIPTION: Verilator: --protect-lib example module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

// See also https://verilator.org/guide/latest/examples.html"

module top (input clk);

  int cyc;
  logic reset_l;
  logic [31:0] a;
  logic [31:0] b;
  logic [31:0] x;

  verilated_secret secret (.a, .b, .x, .clk, .reset_l);

  always @(posedge clk) begin
    $display("[%0t] cyc=%0d a=%0d b=%0d x=%0d", $time, cyc, a, b, x);
    cyc <= cyc + 1;
    if (cyc == 0) begin
      reset_l <= 0;
      a <= 0;
      b <= 0;
    end
    else if (cyc == 1) begin
      reset_l <= 1;
      a <= 5;
      b <= 7;
    end
    else if (cyc == 2) begin
      a <= 6;
      b <= 2;
    end
    else if (cyc == 3) begin
      a <= 1;
      b <= 9;
    end
    else if (cyc > 4) begin
      $display("Done");
      $finish;
    end
  end

endmodule
