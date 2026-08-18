// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Sub;
  typedef enum bit [1:0] {
    ONE,
    TWO,
    THREE,
    FOUR
  } enum_t;

  rand bit num;
  rand enum_t en;

  constraint c {num == 0;}

endclass

class Top;
  rand Sub s;

  function new();
    s = new;
  endfunction
endclass

module t;
  Top top;
  initial begin
    int randomize_result;
    top = new;

    randomize_result = top.randomize();
    `checkd(randomize_result, 1);
    `checkd(top.s.num, 0);

    $write("*-* All Finished *-*\n");
    $finish();
  end
endmodule
