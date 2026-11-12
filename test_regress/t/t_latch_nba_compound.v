// DESCRIPTION: Verilator: Behavioral always_latch reading values change detection can't compare
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: cyc=%0d got=%0d exp=%0d\n", `__FILE__,`__LINE__, cyc, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Cls;
  int v;
  function new(int x);
    v = x;
  endfunction
endclass

module t (
    input clk
);
  int cyc = 0;
  string str = "";
  int q[$];
  Cls h = new(0);
  logic en = 0;  // Stays open while the values below change
  always @(posedge clk) begin
    cyc <= cyc + 1;
    en <= 1;
    str <= {str, "x"};
    q.push_back(cyc);
    h = new(cyc);
  end

  // Such a latch is still scheduled as combinational logic
  int str_len, q_size, h_v;
  // verilator lint_off COMBDLY
  always_latch if (en) str_len <= str.len();
  always_latch if (en) q_size <= q.size();
  always_latch if (en) h_v <= h.v;
  // verilator lint_on COMBDLY

  always @(negedge clk) begin
    if (cyc > 1) begin
      `checkd(str_len, str.len());
      `checkd(q_size, q.size());
      `checkd(h_v, h.v);
    end
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
