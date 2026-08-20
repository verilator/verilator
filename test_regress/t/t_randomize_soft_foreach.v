// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

class Cls1;
  rand int arr[10];
  constraint c_cls {
    soft foreach(arr[i]) arr[i] == i;
  }
endclass

class Cls2;
  rand int arr[10];
  constraint c_cls {
    soft foreach(arr[i]) arr[i] == i;
    arr[1] == 10;
  }
endclass

class Cls3;
  rand int arr[10];
  constraint c_cls {
    soft foreach(arr[i]) arr[i] < i;
    arr[5] == 3;
  }
endclass

module t;
  Cls1 cls1;
  Cls2 cls2;
  Cls3 cls3;
  int ok;

  initial begin
    cls1 = new;
    cls2 = new;
    cls3 = new;
    ok = cls1.randomize();
    `checkd(ok, 1);
    foreach(cls1.arr[i]) begin
      if (cls1.arr[i] != i) $stop;
    end

    ok = cls2.randomize();
    `checkd(ok, 1);
    foreach(cls2.arr[i]) begin
      if (i != 1)
        if (cls2.arr[i] != i) $stop;
    end
    if (cls2.arr[1] != 10) $stop;

    repeat (10) begin
      ok = cls3.randomize();
      `checkd(ok, 1);
      foreach(cls3.arr[i]) begin
        if (cls3.arr[i] >= i) $stop;
      end
      if (cls3.arr[5] != 3) $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
