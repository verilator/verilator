// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   logic clk1 = 0;

   assign #3 clk1 = ~clk1;

   logic clk2 = 0;
   assign #11 clk2 = ~clk2;

   int a1 = 0;
   int b1 = 0;
   always @(posedge clk1) #4 a1 = a1 + 1;
   always @(posedge clk1) @(posedge clk2) b1 = b1 + 1;

   int a2 = 0;
   always_comb begin
       // verilator lint_off MULTIDRIVEN
       a2 = a1 << 1;
       // verilator lint_on MULTIDRIVEN
`ifdef TEST_VERBOSE
       $display("[%0t] a2 = %0d", $time, a2);
`endif
   end

   int b2 = 0;
   always_comb begin
       // verilator lint_off MULTIDRIVEN
       b2 = b1 << 2;
       // verilator lint_on MULTIDRIVEN
`ifdef TEST_VERBOSE
       $display("[%0t] b2 = %0d", $time, b2);
`endif
   end

   int c1 = 0;
   int c2 = 0;
   always @(b2, c1) begin
      c2 = c1 >> 3;
      c1 = b2 << 3;
   end

   always @(posedge clk1) if (a2 != a1 << 1) $stop;
   always @(posedge clk2) #1 if (b2 != b1 << 2) $stop;

   initial #78 begin
`ifdef TEST_VERBOSE
       $display("a1=%0d, b1=%0d, a2=%0d, b2=%0d, c1=%0d, c2=%0d", a1, b1, a2, b2, c1, c2);
`endif
       if (a1 != 12) $stop;
       if (b1 != 4) $stop;
       if (a2 != a1 << 1) $stop;
       if (b2 != b1 << 2) $stop;
       if (c1 != b2 << 3) $stop;
       if (c2 != c1 >> 3) $stop;
       $write("*-* All Finished *-*\n");
       $finish;
   end
endmodule
