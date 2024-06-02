// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class ClsDup;
   int vardup;
   int vardup;
   task memdup;
   endtask
   task memdup;
   endtask

   function void funcdup;
   endfunction
   function void funcdup;
   endfunction

endclass

module t (/*AUTOARG*/);
endmodule
