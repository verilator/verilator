// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define DELAY_INIT_CHECK(foo, bar) \
  assign #1 bar = foo; \
\
  always @(foo, bar) begin \
    $display("%d foo %x, bar %x", $time, foo, bar); \
  end \
\
  initial begin \
    #5 \
    if (bar != foo) $stop; \
    #5 foo = ~foo; \
    #5 \
    if (bar != foo) $stop; \
    #5 foo = ~foo; \
    #5; \
    if (bar != foo) $stop; \
  end \


module t ();
  reg foo1;
  wire bar1;
  initial foo1 = '0;
  `DELAY_INIT_CHECK(foo1, bar1)

  reg foo2 = '0;
  wire bar2;
  `DELAY_INIT_CHECK(foo2, bar2)

  reg foo3 = '0;
  reg bar3 = '1;
  `DELAY_INIT_CHECK(foo3, bar3)

  initial begin
    #30;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
