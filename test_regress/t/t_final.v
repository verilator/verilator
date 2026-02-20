// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 Charlie Brej
// SPDX-License-Identifier: CC0-1.0

module submodule ();
   // This bug only appears when not inlining
   // verilator no_inline_module
   initial begin
      $write("d");
   end
   final begin
      $write("d");
   end
   final ;  // Empty test
endmodule

module t ();
   generate
      for (genvar i = 0; i < 100; i = i + 1) begin : module_set
         submodule u_submodule();
      end
   endgenerate
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
