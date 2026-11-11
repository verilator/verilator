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

  // s_eventually is supported as the consequent of a chain of |-> and |=> whose antecedents have
  // no sequence operator, with a boolean operand; an exact [*1] around the operand or an
  // antecedent is accepted (b[*1] is b). Reported, one message per assertion: s_eventually
  // anywhere else, also under always or s_always; an antecedent with a sequence operator, also
  // a[*1:1]; a |=> that is not the outermost implication; disable iff, also a module default, in
  // a multi-cycle property (here one with a |=> or a [*1]; a |-> s_eventually b is not
  // multi-cycle and is not reported); an operand with a sequence or property operator, or with a
  // sampled value function, also a global clocking one
  logic a = 0, b = 0, c = 0;
  global clocking @(posedge clk);
  endclocking
  assert property (@(posedge clk) (a ##1 a) |-> s_eventually b);
  assert property (@(posedge clk) a[*1:2] |=> s_eventually b);
  assert property (@(posedge clk) a |-> c |=> s_eventually b);
  assert property (@(posedge clk) a |-> c |=> c |=> s_eventually b);
  assert property (@(posedge clk) a |=> not s_eventually b);
  assert property (@(posedge clk) not (a |=> s_eventually b));
  assert property (@(posedge clk) a |-> (s_eventually b) and c);
  assert property (@(posedge clk) a #=# s_eventually b);
  assert property (@(posedge clk) always [0:2] s_eventually b);
  assert property (@(posedge clk) always [1:$] s_eventually b);
  assert property (@(posedge clk) s_always [1:2] s_eventually b);
  assert property (@(posedge clk) a |-> always [0:2] s_eventually b);
  assert property (@(posedge clk) disable iff (c) a |=> s_eventually b);
  assert property (@(posedge clk) disable iff (c) a |-> s_eventually b[*1]);
  assert property (@(posedge clk) disable iff (c) a[*1] |-> s_eventually b);
  assert property (@(posedge clk) disable iff (c) s_eventually b[*1]);
  assert property (@(posedge clk) a |=> s_eventually b[*2]);
  assert property (@(posedge clk) a |-> s_eventually b[*2]);
  assert property (@(posedge clk) a |-> s_eventually b[*1:2]);
  assert property (@(posedge clk) a |-> s_eventually b[+]);
  assert property (@(posedge clk) a |-> s_eventually b[*0:1]);
  assert property (@(posedge clk) a |=> s_eventually b[*1:1]);
  assert property (@(posedge clk) a[*1:1] |=> s_eventually b);
  assert property (@(posedge clk) a |=> s_eventually $rose(b));
  assert property (@(posedge clk) a |-> s_eventually $past(b));
  assert property (@(posedge clk) a |-> s_eventually (c && $changed(b)));
  assert property (@(posedge clk) a |-> s_eventually $fell(b));
  assert property (@(posedge clk) a |-> s_eventually $rose_gclk(b));
  assert property (@(posedge clk) a |-> s_eventually $future_gclk(b));
  assert property (@(posedge clk) a |-> s_eventually $rising_gclk(b));
  assert property (@(posedge clk) a |-> s_eventually $falling_gclk(b));
  assert property (@(posedge clk) a |-> s_eventually $steady_gclk(b));
  assert property (@(posedge clk) a |-> s_eventually $changing_gclk(b));
  assert property (@(posedge clk) a |-> s_eventually (b or c));
  assert property (@(posedge clk) a |-> s_eventually (b ##1 c));
  // The operand is checked after its named sequences and properties are inlined; a named
  // property is reported at its body
  sequence s_seq; b ##1 c; endsequence
  sequence s_rose; $rose(b); endsequence
  property p_seq;
    s_eventually s_seq;
  endproperty
  property p_rose;
    s_eventually s_rose;
  endproperty
  assert property (@(posedge clk) a |-> p_seq);
  assert property (@(posedge clk) a |-> p_rose);
  always @(posedge clk) assert property (a |=> s_eventually s_rose);
  // s_eventually beside a multi-cycle operand of or, with a fail action only
  assert property (@(posedge clk) (s_eventually b) or (a ##1 c))
  else $display("fail");
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
  // An unsupported part of the chain is reported before the disable iff
  assert property (@(posedge clk) a |-> b |=> s_eventually a);
endmodule
