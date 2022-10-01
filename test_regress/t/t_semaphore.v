// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Methods defined by IEEE:
//  class semaphore;
//     function new(int keyCount = 0);
//     function void put(int keyCount = 1);
//     task get(int keyCount = 1);
//     function int try_get(int keyCount = 1);
//  endclass

module t(/*AUTOARG*/);
   // From UVM:
   semaphore s;
   semaphore s2;
   int       msg;

   initial begin
      s = new(4);
      if (s.try_get() != 0) $stop;

      s.put();
      s.get();

      s.put(2);
      s.get(2);

      s.put(2);
      if (s.try_get(2) <= 0) $stop;

`ifndef VERILATOR
      fork
         begin
            #10;  // So later then get() starts below
            s.put(1);
            s.put(1);
         end
         begin
            if (s.try_get(1) != 0) $stop;
            s.get();  // Blocks until put
            s.get();
         end
      join
`endif

      s2 = new;
      if (s2.try_get() != 0) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
