// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Iru Cai.
// SPDX-License-Identifier: CC0-1.0

class Cls1;
   int ctr;
   task run();
      $display("%d", ctr);
      ctr = ctr + 1;
   endtask: run
endclass;

class Cls2 extends Cls1;
   task runtask();
      run();
      run();
      run();
      run();
      run();
      run();
   endtask: runtask
endclass

module top;
   Cls2 o;
   initial begin
      o = new;
      o.runtask();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
