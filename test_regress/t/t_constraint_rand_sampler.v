// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Repeated randomize() of each kind of constraint set: scalars (UniGen2 and
// diversity pins by default), an array (XOR diversity rounds) and
// solve...before (phased, with a diversity round per layer), and a randc
// cycle. The driver checks which solver queries each run sends.

module t;

  class Scalars;
    rand bit [6:0] a;
    rand bit [14:0] b;
    constraint c {
      a < 7'd100;
      b > 15'(a);
    }
  endclass

  class Elems;
    rand bit [30:0] q[3];
    constraint c {foreach (q[i]) q[i] < 31'd1000;}
  endclass

  class Ordered;
    rand bit [4:0] x;
    rand bit [32:0] y;
    constraint c {
      solve x before y;
      x < 5'd20;
      y <= 33'(x);
    }
  endclass

  class Cyclic;
    randc bit [2:0] r;
  endclass

  initial begin
    Scalars s;
    Elems e;
    Ordered o;
    Cyclic c;
    int randomize_result;
    bit [14:0] first_b;
    bit [30:0] first_q0;
    bit b_varied;
    bit q0_varied;
    bit [7:0] seen;
    s = new;
    e = new;
    o = new;
    c = new;
    for (int i = 0; i < 20; ++i) begin
      randomize_result = s.randomize();
      `checkd(randomize_result, 1);
      `checkd(s.a < 7'd100, 1'b1);
      `checkd(s.b > 15'(s.a), 1'b1);
      if (i == 0) first_b = s.b;
      else if (s.b != first_b) b_varied = 1'b1;
      randomize_result = e.randomize();
      `checkd(randomize_result, 1);
      foreach (e.q[j]) `checkd(e.q[j] < 31'd1000, 1'b1);
      if (i == 0) first_q0 = e.q[0];
      else if (e.q[0] != first_q0) q0_varied = 1'b1;
      randomize_result = o.randomize();
      `checkd(randomize_result, 1);
      `checkd(o.x < 5'd20, 1'b1);
      `checkd(o.y <= 33'(o.x), 1'b1);
    end
    // Only Verilator's sampler promises varied results; the solver's depend on the solver
    if ($test$plusargs("check_varied")) begin
      `checkd(b_varied, 1'b1);
      `checkd(q0_varied, 1'b1);
    end

    // Two full randc cycles: the second exhausts the first's history and retries
    repeat (2) begin
      seen = '0;
      repeat (8) begin
        randomize_result = c.randomize();
        `checkd(randomize_result, 1);
        `checkd(seen[c.r], 1'b0);
        seen[c.r] = 1'b1;
      end
    end

    // randomize(null) only checks the current values: no sampling, values unchanged
    s.a = 7'd5;
    s.b = 15'd6;
    randomize_result = s.randomize(null);
    `checkd(randomize_result, 1);
    `checkd(s.a, 5);
    `checkd(s.b, 6);
    s.b = 15'd5;
    randomize_result = s.randomize(null);
    `checkd(randomize_result, 0);
    `checkd(s.a, 5);
    `checkd(s.b, 5);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
