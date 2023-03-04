// DESCRIPTION: Verilator: Verilog Test module
//
// This test examines Verilator against paramter definition with functions.
// Particularly the function takes in argument which is multi-dimentional.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   sub sub();
endmodule

module sub
  #(parameter type T = type(bit[9:0]) )
   ();

   type(bit[9:0]) tvar;

   initial begin
      if ($bits(T) != 10) $stop;
      if ($bits(tvar) != 10) $stop;
      $finish;
   end
endmodule
