// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface class Icls;
   localparam IP = 1;
   typedef int i_t;
endclass

class Cls implements Icls;
   function void f;
      $display(IP); // Bad
   endfunction
endclass

module t (/*AUTOARG*/);
   Cls c;
endmodule
