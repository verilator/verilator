// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   mailbox #(int) mbox;

   task main();
      // See issue #4323; not an INFINITELOOP due to delay inside get()
      forever begin
         int i;
         mbox.get(i);
         $display("[%0t] Got %0d", $time, i);
      end
   endtask

   initial begin
      mbox = new (1);

      #10;
      fork
         main();
      join_none

      #10;
      mbox.put(10);
      mbox.put(11);

      #10;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
