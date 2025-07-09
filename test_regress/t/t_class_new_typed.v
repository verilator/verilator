// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t ();
class SuperCls;
   int s = 2;
   function new(int def = 3);
      s = def;
   endfunction
endclass

class Cls extends SuperCls;
   function new(int def = 42);
      s = def;
   endfunction
endclass

   SuperCls super_obj;

   initial begin
      super_obj = Cls::new;
      if (super_obj.s != 42) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
