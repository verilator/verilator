// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2016 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// issue 1991

module t
  (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   socket #(3'b000) s0();
   socket #(3'b010) s1();
   socket #(2'b10) s2();
   socket #(2'b11) s3();

   always_ff @ (posedge clk) begin
      if (s0.ADDR != 0) $stop;
      if (s1.ADDR != 2) $stop;
      if (s2.ADDR != 2) $stop;
      if (s3.ADDR != 3) $stop;
      if ($bits(s0.ADDR) != 3) $stop;
      if ($bits(s1.ADDR) != 3) $stop;
      if ($bits(s2.ADDR) != 2) $stop;
      if ($bits(s3.ADDR) != 2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module socket #(ADDR)();
   initial
     $display("bits %0d, addr %b", $bits(ADDR), ADDR);
endmodule
