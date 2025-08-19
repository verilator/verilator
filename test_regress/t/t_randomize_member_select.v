// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
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
  initial begin
    a = new;
    i = 7;
    repeat (120) begin
      assert (a.randomize() with {if (a.delay == 1) a.rdata == i;} != 0);
      assert (a.b.randomize() with {a.b.insideB < 3;} != 0);
      if (a.delay == 1 && a.rdata != 97) $stop;
      if (a.b.insideB >= 3) $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
