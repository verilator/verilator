// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;
  logic clk = 0;
  int cyc = 0;
  int unsel = 0;

  sub1 sub1a (.*);
  sub1 sub1b (.*);
  sub1 \esc.inst  (.*);
  for (genvar i = 0; i < 2; ++i) begin : gen
    sub2 sub (.*);
  end
  sub3 sub3 (.*);

  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars(1, clk, cyc);  // Variables
    $dumpvars(2, sub1a);  // Scope and one level below
    $dumpvars(1, t.sub1b.value);  // Variable under a scope
    $dumpvars(0, \esc.inst .sub2b);  // Scope with a dot in its name
    $dumpvars(0, gen[1].sub);  // Generate array element
  end

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    unsel <= unsel + 2;
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

module sub1 (
    input int cyc
);
  int value;
  always_comb value = cyc + 1;
  sub2 sub2a (.*);
  sub2 sub2b (.*);
endmodule

module sub2 (
    input int cyc
);
  int value;
  always_comb value = cyc + 2;
endmodule

module sub3 (
    input int cyc
);
  int value;
  always_comb value = cyc + 3;
  sub2 sub2a (.*);
  initial begin
    $dumpvars(1, sub2a);  // Under this instance
    $dumpvars(1, sub1b.sub2a);  // Found upward
  end
endmodule
