// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2015 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// bug1005

module foo_module;
   generate
      for (genvar i = 0; i < 2; i = i + 1) begin : my_gen_block
         logic baz;
      end
   endgenerate
endmodule

module bar_module;
   foo_module foo();
endmodule

module t;
   bar_module bar();
   initial begin
      bar.foo.my_gen_block[0].baz = 1;
      if (bar.foo.my_gen_block[0].baz) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
