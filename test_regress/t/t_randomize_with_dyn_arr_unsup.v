// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef int int_arr_t[];

class C;
  rand int x;
  rand bit foo;
endclass

class Cls4;
  int_arr_t arr;
  task body();
    C c;
    c = new;
    arr = new[2];
    arr[0] = 123;
    arr[1] = 124;
    repeat (40) begin
      if (c.randomize() with {solve foo before x; x == arr[foo]; foo <= 1;} != 1) $stop;
      `checkd(c.x, arr[c.foo]);
    end
  endtask
endclass

module t;
  Cls4 c4;
  initial begin
    c4 = new;
    c4.body();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
