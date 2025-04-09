// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);

class Base;
   int m_s = 2;
   function new(int def = 3);
      m_s = def;
   endfunction
endclass

class Cls5Exp extends Base(5);
   int m_a = 11;
   function new(int def = 42);  // Explicit new
      m_a = def;
   endfunction
endclass

class Cls5Imp extends Base(5);
   int m_a = 12;
   // Implicit new
endclass

module t ();

   Cls5Exp ce;
   Cls5Imp ci;

   initial begin
      ce = new(37);
      `checkh(ce.m_s, 5);
      `checkh(ce.m_a, 37);
      ci = new;
      `checkh(ci.m_s, 5);
      `checkh(ci.m_a, 12);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
