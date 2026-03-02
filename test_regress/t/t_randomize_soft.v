// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test soft constraint solving per IEEE 1800-2017 section 18.5.13

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

// Case 1: Only soft, no hard -- soft should be satisfied
class Case1;
  rand int x;
  constraint c_soft { soft x == 5; }
endclass

// Case 2: Two soft on same var -- last-wins (c_b declared after c_a)
class Case2;
  rand int x;
  constraint c_a { soft x == 5; }
  constraint c_b { soft x == 10; }
endclass

// Case 3: Soft on different vars -- both should be satisfied
class Case3;
  rand int x;
  rand int y;
  constraint c_x { soft x == 7; }
  constraint c_y { soft y == 3; }
endclass

// Case 4: Soft range partially covered by hard -- SAT at intersection
class Case4;
  rand int x;
  constraint c_soft { soft x inside {[1:10]}; }
  constraint c_hard { x inside {[5:15]}; }
endclass

// Case 5: Soft completely overridden by hard -- hard wins
class Case5;
  rand int x;
  constraint c_soft { soft x == 5; }
  constraint c_hard { x > 10; }
endclass

module t;
  Case1 c1;
  Case2 c2;
  Case3 c3;
  Case4 c4;
  Case5 c5;
  int rand_ok;

  initial begin
    c1 = new;
    c2 = new;
    c3 = new;
    c4 = new;
    c5 = new;

    repeat (20) begin
      // Case 1: only soft, no hard -- soft satisfied
      rand_ok = c1.randomize();
      `checkd(rand_ok, 1)
      `checkd(c1.x, 5)

      // Case 2: two soft on same var -- last-wins
      rand_ok = c2.randomize();
      `checkd(rand_ok, 1)
      `checkd(c2.x, 10)

      // Case 3: soft on different vars -- both satisfied
      rand_ok = c3.randomize();
      `checkd(rand_ok, 1)
      `checkd(c3.x, 7)
      `checkd(c3.y, 3)

      // Case 4: soft range partially covered by hard -- intersection [5:10]
      rand_ok = c4.randomize();
      `checkd(rand_ok, 1)
      `check_range(c4.x, 5, 10)

      // Case 5: soft completely overridden by hard -- hard wins
      rand_ok = c5.randomize();
      `checkd(rand_ok, 1)
      if (c5.x <= 10) begin
        $write("%%Error: %s:%0d: x=%0d should be > 10\n", `__FILE__, `__LINE__, c5.x);
        `stop;
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
