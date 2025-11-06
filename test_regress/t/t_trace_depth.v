// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc;
  wire integer value_at_top = cyc;  // Magic name checked in .py file

  sub1 sub1a (.*);
  sub1 sub1b (.*);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sub1 (
    input int cyc
);

  sub2 sub2a (.*);
  sub2 sub2b (.*);
  sub2 sub2c (.*);
endmodule

module sub2 (
    input int cyc
);

  wire integer value_in_sub = cyc;  // Magic name checked in .py file
endmodule
