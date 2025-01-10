// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   function int fi();
      return 10;
   endfunction
   static function int sfi();
      return 10;
   endfunction
endclass

module t;
   function int f1;
      return 20;
   endfunction

   initial begin
      Cls c;
      //
      f1();  // Bad - ignored result
      //
      c = new;
      c.fi();  // Bad - ignored result
      c.sfi();  // Bad - ignored result
      //
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
