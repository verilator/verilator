// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk = 0;
  initial forever #1 clk = ~clk;

  localparam MAX = 3;
  integer cyc = 1;

  assert property (@(posedge clk) s_eventually ##1 1);
  assert property (@(negedge clk) s_eventually ##1 1);

  // s_eventually is supported only with a boolean operand, as the consequent of |-> or |=>
  // whose antecedents have no sequence operator, where a |=> must be the outermost implication
  logic a = 0, b = 0, c = 0;
  assert property (@(posedge clk) (a ##1 a) |-> s_eventually b);
  assert property (@(posedge clk) a[*1:2] |=> s_eventually b);
  assert property (@(posedge clk) a |-> c |=> s_eventually b);
  assert property (@(posedge clk) a |=> not s_eventually b);
  assert property (@(posedge clk) not (a |=> s_eventually b));
  assert property (@(posedge clk) a |-> (s_eventually b) and c);
  assert property (@(posedge clk) a #=# s_eventually b);
  assert property (@(posedge clk) disable iff (c) a |=> s_eventually b);
  assert property (@(posedge clk) a[*1] |=> s_eventually b);
  assert property (@(posedge clk) a |=> s_eventually b[*2]);
  assert property (@(posedge clk) a |-> s_eventually b[*2]);
  assert property (@(posedge clk) a |-> s_eventually (b or c));
  assert property (@(posedge clk) a |-> s_eventually (b ##1 c));
  // An if/case property with s_eventually in a branch, also with a pass action
  assert property (@(posedge clk) case (c) 1'b1: s_eventually b; default: a |=> b; endcase)
    $display("pass");
  assert property (@(posedge clk) if (c) s_eventually b else (a[=1]))
    $display("pass");
  always @(posedge clk) assert property (a |=> s_eventually b[*2]);
  sub u_sub (.clk(clk), .rst(c), .a(a), .b(b));

  always @(posedge clk) begin
    ++cyc;
    if (cyc == MAX) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

// A module default disable iff applies too
module sub (
    input clk,
    input rst,
    input a,
    input b
);
  default disable iff (rst);
  assert property (@(posedge clk) a |=> s_eventually b);
  assert property (@(posedge clk) b |=> s_eventually a);
endmodule
