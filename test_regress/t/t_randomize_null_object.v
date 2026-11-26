// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

class SimpleRandClass;
  rand bit [7:0] value;
  constraint value_con {value > 0 && value < 200;}
  function new();
  endfunction
endclass

class Counted;
  rand bit value;
  int calls;
  static int bound_calls;
  function void post_randomize();
    ++calls;
  endfunction
  static function int bound();
    ++bound_calls;
    return 1;
  endfunction
endclass

int cnt;

function automatic int idx();
  ++cnt;
  return 1;
endfunction

module t;
  SimpleRandClass obj;
  int rand_result;
  SimpleRandClass h[3];

  initial begin
    obj = null;
    rand_result = obj.randomize();
    `checkd(rand_result, 0);

    obj = new();
    rand_result = obj.randomize();
    `checkd(rand_result, 1);
    `check_range(obj.value, 1, 199);

    // A target with side effects is evaluated once
    foreach (h[i]) h[i] = new;
    rand_result = h[idx()].randomize();
    `checkd(rand_result, 1);
    `checkd(cnt, 1);
    rand_result = h[idx()].randomize() with {value > 100;};
    `checkd(rand_result, 1);
    `checkd(cnt, 2);
    `check_range(h[1].value, 101, 199);

    // A call tested against a set is evaluated once
    begin
      Counted c;
      bit ok;
      c = new;
      ok = c.randomize() inside {0, 1};
      `checkd(ok, 1);
      `checkd(c.calls, 1);
      ok = c.randomize() with {value == 1'b1;} inside {0, 1};
      `checkd(ok, 1);
      `checkd(c.calls, 2);
      `checkd(c.value, 1);
    end
    // Likewise in an array method 'with' clause
    begin
      Counted c;
      int q[$];
      bit ok;
      c = new;
      q = '{1, 2};
      ok = (q.sum() with (int'(c.randomize() with {int'(value) <= Counted::bound();}))) inside {[0 : 10]};
      `checkd(ok, 1);
      `checkd(c.calls, 2);
      `checkd(Counted::bound_calls, 2);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
