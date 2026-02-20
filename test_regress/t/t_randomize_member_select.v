// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

class B;
  rand int insideB;
  constraint i {
    insideB inside {[0:10]};
  };
endclass

class A;
  rand logic[31:0] rdata;
  rand int delay;
  int i = 97;
  rand B b;
  function new();
    b = new;
  endfunction
  constraint delay_bounds {
    delay inside {[0:2]};
  }
endclass

module t;
  A a;
  int i;
  int delay;
  logic[31:0] rdata;
  int b;
  initial begin
    a = new;
    i = 7;
    repeat (120) begin
      a.b.insideB = 3;
      a.delay = 1;
      a.rdata = 3;
      if (a.randomize() with {if (a.delay == 1) a.rdata == i;} == 0) $stop;
      if (a.b.randomize() with {a.b.insideB < 3;} == 0) $stop;
      if (a.delay == 1 && a.rdata != 97) $stop;
      if (a.b.insideB >= 3) $stop;
      if (a.randomize() with {if (a.delay == 1) a.rdata == local::i;} == 0) $stop;
      if (a.delay == 1 && a.rdata != 7) $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
