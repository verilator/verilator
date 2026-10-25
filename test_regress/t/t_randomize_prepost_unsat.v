// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Anirudh Sahu
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// IEEE 1800-2023 18.6.3: "If randomize() fails, post_randomize() is not called."

class Inner;
  rand bit [14:0] p;
  int pre_calls;
  int post_calls;
  function void pre_randomize();
    pre_calls++;
  endfunction
  function void post_randomize();
    post_calls++;
  endfunction
endclass

class Outer;
  rand bit [6:0] c;
  rand Inner inner;
  int pre_calls;
  int post_calls;
  constraint bad {
    c > 100;
    c < 50;
  }
  function new();
    inner = new;
  endfunction
  function void pre_randomize();
    pre_calls++;
  endfunction
  function void post_randomize();
    post_calls++;
  endfunction
endclass

class Base;
  rand bit [6:0] c;
  constraint bad {
    c > 100;
    c < 50;
  }
endclass

class Derived extends Base;
  int post_calls;
  function void post_randomize();
    post_calls++;
  endfunction
endclass

module t;
  initial begin
    Outer obj;
    Base b;
    Derived d;
    int ok;

    obj = new;
    ok = obj.randomize();
    `checkd(ok, 0);
    ok = obj.randomize() with {c == 1;};
    `checkd(ok, 0);
    `checkd(obj.pre_calls, 2);
    `checkd(obj.inner.pre_calls, 2);
    `checkd(obj.post_calls, 0);
    `checkd(obj.inner.post_calls, 0);

    obj.bad.constraint_mode(0);
    ok = obj.randomize();
    `checkd(ok, 1);
    ok = obj.randomize() with {c == 1;};
    `checkd(ok, 1);
    `checkd(obj.post_calls, 2);
    `checkd(obj.inner.post_calls, 2);

    // randomize() with through a base handle uses the virtual post_randomize wrapper
    d = new;
    b = d;
    ok = b.randomize() with {c == 1;};
    `checkd(ok, 0);
    `checkd(d.post_calls, 0);

    d.bad.constraint_mode(0);
    ok = b.randomize() with {c == 1;};
    `checkd(ok, 1);
    `checkd(d.post_calls, 1);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
