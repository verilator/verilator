// DESCRIPTION: Verilator: Demonstrate deferred linking across module
// bondaries
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

module m1();
   logic v1;
endmodule

module t (/*AUTOARG*/);
   for (genvar the_genvar = 0; the_genvar < 4; the_genvar++) begin : m1_b
      m1 m1_inst();
   end
   for (genvar the_other_genvar = 0; the_other_genvar < 4; the_other_genvar++) begin
      always_comb m1_b[the_other_genvar].m1_inst.v1 = 1'b0;
   end

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
