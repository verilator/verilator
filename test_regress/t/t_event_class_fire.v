// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   event e;
   task trig_e();
      ->> e;
   endtask
endclass

module top();
   event e;
   initial begin
      Cls c;
      c = new;
      c.trig_e();
      wait(e.triggered);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
