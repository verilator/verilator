// DESCRIPTION: Verilator: Package and module sharing a name
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 3.13: Packages and modules are in separate name spaces,
// but both have state here, so both must get their own generated class.

package foo;
  int count = 10;
  function automatic int next();
    count++;
    return count;
  endfunction
endpackage

module bar (
    input clk,
    output int o
);
  /*verilator no_inline_module*/
  int r = 30;
  always @(posedge clk) r <= r + 1;
  assign o = r;
endmodule

package bar;
  int count = 40;
  function automatic int next();
    count++;
    return count;
  endfunction
endpackage

module t;
  logic clk = 0;
  int foo_o;
  int bar_o;
  // Autoloading foo rescans bar, whose package has already been renamed.
  foo u_foo (
      .clk(clk),
      .o(foo_o)
  );
  bar u_bar (
      .clk(clk),
      .o(bar_o)
  );

  initial begin
    #1 clk = 1;
    #1;
    if (foo::next() != 11) $stop;
    if (foo_o != 21) $stop;
    if (bar_o != 31) $stop;
    if (bar::next() != 41) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
