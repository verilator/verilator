// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   event a, b;

   int   order = 0;

   initial begin
      order++; if (order != 1) $stop;
      #10;
      $display("[%0t]%0d -> a", $time, order);
      order++; if (order != 2) $stop;
      -> a;
      #10;
      $display("[%0t]%0d -> b", $time, order);
      order++; if (order != 4) $stop;
      -> b;
      #100;
      order++; if (order != 6) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

   always @ (a or b) begin
      $display("[%0t]%0d entering", $time, order);
      order++; if (order != 3) $stop;
      #15;
      $display("[%0t]%0d 15 later", $time, order);
      order++; if (order != 5) $stop;
   end
endmodule
