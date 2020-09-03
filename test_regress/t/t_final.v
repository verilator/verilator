// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Charlie Brej.
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
