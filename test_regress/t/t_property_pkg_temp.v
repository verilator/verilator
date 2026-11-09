// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A temporary made for the body of a package property, used from several modules

package pkg;
  // Impure left operand of 'inside', evaluated once through a temporary
  property p_inside;
    ($urandom(1) & 32'h0) inside {32'h0, 32'h1};
  endproperty
endpackage

module sub (
    input clk
);
  assert property (@(posedge clk) pkg::p_inside);
endmodule

module t (
    input clk
);
  int cyc = 0;

  sub u_sub (.clk(clk));
  assert property (@(posedge clk) pkg::p_inside);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
