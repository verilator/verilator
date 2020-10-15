// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   class Cls;
      int que[$];

      task push_data(int val);
         que.push_back(val);
      endtask
   endclass

   initial begin
      Cls c2 [1:0];

      c2[0] = new();

      c2[0].push_data(20);   // Works

      if (c2[0].que.size() != 1) $stop;

      c2[0].que.push_back(10); // Unsupported
      if (c2[0].que.size() != 2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
