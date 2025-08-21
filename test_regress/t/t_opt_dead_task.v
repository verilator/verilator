// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
   // AstLet and AstProperty are also NodeFTasks, but lets are substituted earlier and properties should be "used" by their asserts so also not deadified
   let nclk = ~clk;
   assert property(@(posedge clk)1);

   function void livefunc();
   endfunction
   task livetask;
   endtask
   // Tasks/functions that are called somewhere will not be deadified
   initial begin
      livefunc();
      livetask();
      $finish;
   end

   // These should be deadified
   function deadfunc();
   endfunction
   task deadtask;
   endtask
endmodule
