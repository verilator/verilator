// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2020 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t_tautological_bitwise_compare(clk);
   input clk;

   reg   x = 0;

   always @(posedge clk) begin
      if (!x) begin
         // These used to trigger a warning with clang 10.0.0:
         // error: bitwise comparison always evaluates to false
         // [-Werror,-Wtautological-bitwise-compare]. The body of the 'if' is
         // not important, just not empty so the 'if' remains. Also it cannot
         // be something that causes the condition to get a branch hint like
         // $stop as that seems to suppress the clang warning.

         // Always false bit 1 set on lhs, clear on rhs
         if ({1'h1, x} == 2'h0) x <= '0;
         if ({1'h1, x} == 2'h1) x <= '0;
         if ({1'h1, x} == {1'b0, x}) x <= '0;
         if ({1'h0, x} == {1'b1, x}) x <= '0;
         // Always true for the same reason
         if ({1'h1, x} != 2'h0) x <= '0;
         if ({1'h1, x} != 2'h1) x <= '0;
         if ({1'h1, x} != {1'b0, x}) x <= '0;
         if ({1'h0, x} != {1'b1, x}) x <= '0;

         // Not known up front, but won't get here if x is set
         if ({1'h1, x} == 2'h3) $stop;
         if ({1'h1, x} != 2'h2) $stop;
      end

      // This make sure 'x' is used but not constant so it doesn't get removed
      x <= '1;

      // Done
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
