// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Base;
   int m_s = 2;
   function new(int def = 3);
      m_s = def;
   endfunction
endclass

class Cls5 extends Base(5);
   int m_a;
   function new(int def = 42);
      super.new(33);  // Bad, can't super.new with extends args
      m_a = def;
   endfunction
endclass
