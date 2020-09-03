// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// bug998

module t1(input logic foo);
   initial begin
      $display("%m %d", foo);
   end
endmodule

module t();

   logic [1:0] my_foo;

   generate
      genvar the_genvar;
      for (the_genvar = 0; the_genvar < 2; the_genvar++) begin : TestIf
         //logic tmp_foo;
         //assign tmp_foo = my_foo[the_genvar];
         t1 t (.foo(my_foo[the_genvar]));
         //t1 t (.foo(tmp_foo));
      end
   endgenerate

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
