// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
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

module t;
endmodule
