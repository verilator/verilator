// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class A;
  rand logic[31:0] rdata;
  rand int delay;
  constraint delay_bounds {
    delay inside {[0:2]};
  }
endclass

module t;
  A a;
  initial begin
    a = new;
    repeat (120) begin
      assert (a.randomize() with {if (a.delay == 1) a.rdata == 3;} != 0);
      if (a.delay == 1 && a.rdata != 3) $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
