// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do begin if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%h exp=%h\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end end while(0)
// verilog_format: on

interface I1 #(int N = 1);
  class C #(type T = int);
    typedef T data_t;
  endclass
  C#(bit[N-1:0])::data_t value;
endinterface

interface I2 #(int N = 1);
  bit [N-1:0] value;
  class C;
    virtual I2#(N) vif;
  endclass
  C obj = new;
endinterface

module t;
  I1 #(7) i1();
  I2 #(7) i2();

  initial begin
    `checkh($bits(i1.value), 7);

    i2.obj.vif = i2;
    i2.obj.vif.value = 7'h55;
    `checkh(i2.value, 7'h55);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
