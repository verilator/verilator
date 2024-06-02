// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   reg [7:0] cyc; initial cyc = 0;

   reg [31:0] loops;
   reg [31:0] loops2;

   always @ (posedge clk) begin
      cyc <= cyc+8'd1;
      if (cyc == 8'd1) begin
         $write("[%0t] t_loop: Running\n", $time);
         // Unwind <
         loops = 0;
         loops2 = 0;
         for (int i=0; i<16; i=i+1) begin
            loops = loops + i;          // surefire lint_off_line ASWEMB
            loops2 = loops2 + i;        // surefire lint_off_line ASWEMB
         end
         if (loops !== 120) $stop;
         if (loops2 !== 120) $stop;
         // Check we can declare the same signal twice
         loops = 0;
         for (int i=0; i<=16; i=i+1) begin
            loops = loops + 1;
         end
         if (loops !== 17) $stop;
         // Check type is correct
         loops = 0;
         for (byte unsigned i=5; i>4; i=i+1) begin
            loops = loops + 1;
         end
         if (loops !== 251) $stop;
         // Check large loops
         loops = 0;
         for (int i=0; i<100000; i=i+1) begin
            loops = loops + 1;
         end
         if (loops !== 100000) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
