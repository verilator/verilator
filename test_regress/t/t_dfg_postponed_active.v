// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Keep the clock pin assignment out of the #1 output's Postponed process.
interface intf (
    input bit clk  /*verilator public_flat_rw*/
);
  bit q0;
  bit q1;
  clocking cb @(posedge clk);
    output #0 q0;
    output #1 q1;
  endclocking
endinterface

module endpoint (
    input bit clk  /*verilator public_flat_rw*/
);
  bit q0;
  bit q1;
  clocking cb @(posedge clk);
    output #0 q0;
    output #1 q1;
  endclocking
endmodule

module t;
  bit clk = 1'b0;
  bit expected = 1'b0;
  always #5 clk = ~clk;

  intf i (.clk);
  endpoint m (.clk);

  always @(posedge clk) begin
    expected = ~expected;
    i.cb.q0 <= expected;
    i.cb.q1 <= expected;
    m.cb.q0 <= expected;
    m.cb.q1 <= expected;
  end

  initial begin
    repeat (3) begin
      #8;
      `checkd(i.q0, expected);
      `checkd(i.q1, expected);
      `checkd(m.q0, expected);
      `checkd(m.q1, expected);
      #2;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
