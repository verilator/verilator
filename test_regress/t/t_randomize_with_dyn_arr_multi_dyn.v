// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_rand(cl, field, cond) \
begin \
   automatic longint prev_result; \
   automatic bit ok = 0; \
   if (!bit'(cl.randomize() with {cond;})) $stop; \
   prev_result = longint'(field); \
   if (!(cond)) $stop; \
   repeat(40) begin \
      longint result; \
      if (!bit'(cl.randomize() with {cond;})) $stop; \
      result = longint'(field); \
      if (!(cond)) $stop; \
      if (result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end
// verilog_format: on

typedef int int_arr_t[];

class A;
  rand int x;
endclass

class Cls;
  int_arr_t arr[];
  task body();
    int ok;
    A a;
    a = new;
    arr = new[2];
    arr[1] = new[2];
    arr[1][1] = 123;
    `check_rand(a, a.x, a.x < arr[1][1]);
  endtask
endclass

class B;
  rand int x;
  rand int arr[][];
endclass

class Cls2;
  task body();
    int ok;
    B b;
    b = new;
    b.arr = new[2];
    b.arr[1] = new[2];
    b.x = 1;
    b.arr[1][1] = 2;
    `check_rand(b, b.x, b.x < b.arr[1][1]);
  endtask
endclass

class Cls3;
  rand int_arr_t arr;
  task body();
    int ok;
    B b;
    b = new;
    b.arr = new[2];
    b.arr[1] = new[2];
    b.x = 1;
    b.arr[1][1] = 2;
    arr = new[2];
    arr[1] = 3;
    `check_rand(b, b.x, b.x < b.arr[1][1]);
    `checkd(arr[1], 3);
  endtask
endclass

class Cls4;
  rand int_arr_t arr[];
  task body();
    int ok;
    A a;
    a = new;
    arr = new[2];
    arr[1] = new[2];
    arr[1][1] = 123;
    `check_rand(a, a.x, a.x < arr[1][1]);
  endtask
endclass

module t;
  Cls c;
  Cls2 c2;
  Cls3 c3;
  Cls4 c4;
  initial begin
    c = new;
    c2 = new;
    c3 = new;
    c4 = new;
    c.body();
    c2.body();
    c3.body();
    c4.body();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
