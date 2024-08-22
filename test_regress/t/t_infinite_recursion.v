// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class cls;
   task t; t; endtask
   task pre_randomize;
      t;
   endtask
endclass
module t;
   cls obj;
   task t;
      int _ = obj.randomize() with {1 == 1;};
   endtask
endmodule
