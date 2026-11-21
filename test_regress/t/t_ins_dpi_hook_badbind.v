// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Bound paths that match no instance (s9) or no variable (s2.vv) are reported at time zero
module top_module;
  logic       clk = 0;
  logic [7:0] o1;
  logic [7:0] o2;

  sub s1 (.o(o1));
  sub s2 (.o(o2));

  int cyc = 0;
  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("[%0d] s1=%02x s2=%02x", cyc, o1, o2);
    if (cyc > 3) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule

module sub (
  output logic [7:0] o
);
  logic [7:0] v = 8'h00;
  assign o = v;
endmodule
