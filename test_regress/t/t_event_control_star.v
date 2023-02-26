// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Based on ivtest's nested_impl_event1.v by Martin Whitaker.

module t();

   reg a;
   reg b;
   reg c;

   always @* begin  // @(b or c)
     a = b;
     $display("[%0t] Triggered 1 @(b or c)", $time);

     @* a = c;  // @(c)
     $display("[%0t] Triggered 2 @(c)", $time);
   end

   initial begin
      #10;
      b = 0;
      #10;
      b = 1;
      #10;
      c = 0;
      #10;
      c = 1;
      #10;
      c = 0;
      #10;
      $write("*-* All Finished *-*\n");
      $finish(0);
   end

endmodule
