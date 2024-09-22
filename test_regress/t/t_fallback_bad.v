// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

int f = 5;
task tsk; endtask

package pkg;
endpackage

module subm;
endmodule

module submo;
   subm sub2();
endmodule

module t;
   submo sub1();

   class Base;endclass
   class Cls extends Base;
      task calltsk;
         super.tsk;
         this.tsk;
         super.f = 8;
         this.f = 8;
         sub1.sub2.tsk;
         pkg::f = 8;
         pkg::tsk();
         sub1.sub2.f = 8;
         sub1.sub2.f.f = 8;
      endtask
   endclass

   Cls obj = new;
   initial begin
      obj.calltsk;
      if (f != 5) $stop;
   end
endmodule
