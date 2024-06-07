// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   logic clk = 0, foo = 0, bar = 0;

   always #5 clk = ~clk;

   clocking cb @(posedge clk);
       input #11 output #2 foo;
       inout bar;
   endclocking

   initial begin
       cb.foo <= 1;
       cb.bar <= 1;
       if (foo != 0 || cb.foo != 0) $stop;
       if (bar != 0 || cb.bar != 0) $stop;

       @(posedge bar)
       if ($time != 5) $stop;
       if (foo != 0 || cb.foo != 0) $stop;
       if (cb.bar != 0) $stop;

       #1
       if (foo != 0 || cb.foo != 0) $stop;
       if (cb.bar != 1) $stop;

       @(posedge foo)
       if ($time != 7) $stop;
       if (cb.foo != 0) $stop;

       #9  // $time == 16
       if (cb.foo != 0) $stop;

       #10  // $time == 26
       if (cb.foo != 1) $stop;
       $write("*-* All Finished *-*\n");
       $finish;
   end
endmodule
