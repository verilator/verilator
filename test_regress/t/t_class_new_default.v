// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


class ClsDef;
   int imembera;
   function new(default);
      imembera = i + 1;
   endfunction
endclass

class ClsDefFwd;
   int imembera;
   extern function new(default);
endclass

function ClsDefFwd::new(default);
endfunction

module t (/*AUTOARG*/);
   initial begin
      // TODO real test
      $stop;
   end
endmodule
