// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface class Icls1;
   pure virtual function int icf1;
   pure virtual function int icf2;
endclass

class Cls implements Icls1;
   virtual function int icf1;
      return 1;
   endfunction
   // Bad missing icf2
endclass

module t (/*AUTOARG*/);
   Cls c;
endmodule
