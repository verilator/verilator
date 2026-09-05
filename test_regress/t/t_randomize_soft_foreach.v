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

class Cls4;
  rand int arr[10][20];
  rand bit a;
  constraint c_cls {
    soft foreach(arr[i])
        foreach (arr[i][j])
          soft arr[i][j] == i + j;
    arr[5][10] == 2;
  }
endclass

module t;
  Cls1 cls1;
  Cls2 cls2;
  Cls3 cls3;
  Cls4 cls4;
  int ok;

  initial begin
    cls1 = new;
    cls2 = new;
    cls3 = new;
    cls4 = new;
    ok = cls1.randomize();
    `checkd(ok, 1);
    foreach(cls1.arr[i]) begin
      `checkd(cls1.arr[i], i);
    end

    ok = cls2.randomize();
    `checkd(ok, 1);
    foreach(cls2.arr[i]) begin
      if (i != 1)
        `checkd(cls2.arr[i], i);
    end
    `checkd(cls2.arr[1], 10);

    repeat (10) begin
      ok = cls3.randomize();
      `checkd(ok, 1);
      foreach(cls3.arr[i]) begin
        if (cls3.arr[i] >= i) $stop;
      end
      `checkd(cls3.arr[5], 3);
    end

    ok = cls4.randomize();
    `checkd(ok, 1);
    foreach(cls4.arr[i, j]) begin
      if (i != 5 || j != 10) begin
        `checkd(cls4.arr[i][j], i+j);
      end
    end
    `checkd(cls4.arr[5][10], 2);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
