// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
`define checkd_ne(gotv,expv) do if ((gotv) === (expv)) begin $write("%%Error: %s:%0d:  got=%0d expected any other value\n", `__FILE__,`__LINE__, (gotv)); `stop; end while(0);
// verilog_format: on

typedef int int_arr_t[];

class A;
  rand int x;
endclass

class Cls;
  rand int_arr_t arr;
  function int foo();
    return arr[0];
  endfunction
  task body();
    int ok;
    A a;
    int prev = -1;
    a = new;
    arr = new[2];
    arr[0] = 111112300;
    arr[1] = 123000000;
    repeat (40) begin
      ok = a.randomize() with {
        x >= 0;
        x <= arr[1];
      };
      `checkd(ok, 1);
      `check_range(a.x, 0, 123000000);
      `checkd_ne(a.x, prev);
      prev = a.x;
    end
    prev = -1;
    repeat (40) begin
      ok = a.randomize() with {
        x >= 0;
        x <= foo();
      };
      `checkd(ok, 1);
      `check_range(a.x, 0, 111112300);
      `checkd_ne(a.x, prev);
      prev = a.x;
    end
  endtask
endclass

class B;
  rand int x;
  rand int_arr_t arr;
endclass

class Cls2;
  task body();
    int ok;
    B b;
    int prev = -1;
    b = new;
    b.arr = new[2];
    b.x = 1;
    b.arr[1] = 200000;
    repeat (40) begin
      ok = b.randomize() with {x == arr[1];};
      `checkd(ok, 1);
      `checkd(b.x, b.arr[1]);
      `checkd_ne(b.x, prev);
      prev = b.x;
    end
  endtask
endclass

class Cls3;
  rand int_arr_t arr;
  task body();
    int ok;
    B b;
    int prev = -1;
    b = new;
    b.arr = new[2];
    b.x = 1;
    b.arr[1] = 30000000;
    arr = new[2];
    arr[1] = 3;
    repeat (40) begin
      ok = b.randomize() with {x == arr[1];};
      `checkd(ok, 1);
      `checkd(arr[1], 3);
      `checkd(b.x, b.arr[1]);
      `checkd_ne(b.x, prev);
      prev = b.x;
    end
  endtask
endclass

class address_window;
  rand bit [36:0] lower_bound;
endclass

class access_request;
  rand bit [36:0] offset;
endclass

class Cls4;
  rand address_window windows[];
  task body();
    int ok;
    access_request request;
    request = new;
    windows = new[1];
    windows[0] = new;
    windows[0].lower_bound = 37'h15_2468_ace0;
    repeat (20) begin
      ok = request.randomize() with {offset >= windows[0].lower_bound;};
      `checkd(ok, 1);
      `checkd(request.offset >= windows[0].lower_bound, 1);
      ok = request.randomize() with {offset dist {windows[0].lower_bound := 1};};
      `checkd(ok, 1);
      `checkd(request.offset, windows[0].lower_bound);
      ok = request.randomize() with {
        offset == (windows[0].lower_bound > 0 ? windows[0].lower_bound : offset);
      };
      `checkd(ok, 1);
      `checkd(request.offset, windows[0].lower_bound);
      windows[0].lower_bound += 37'h02_0000_0000;
    end
  endtask
endclass

class Base;
  rand int_arr_t arr;
endclass

class Target extends Base;
  rand int x;
endclass

class Cls5 extends Base;
  task body();
    int ok;
    Target target;
    target = new;
    target.arr = new[1];
    arr = new[1];
    arr[0] = 123;
    ok = target.randomize() with {x == local::arr[0];};
    `checkd(ok, 1);
    `checkd(target.x, 123);
    `checkd(arr[0], 123);
  endtask
endclass

module t;
  Cls c;
  Cls2 c2;
  Cls3 c3;
  Cls4 c4;
  Cls5 c5;
  initial begin
    c = new;
    c2 = new;
    c3 = new;
    c4 = new;
    c5 = new;
    c.body();
    c2.body();
    c3.body();
    c4.body();
    c5.body();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
