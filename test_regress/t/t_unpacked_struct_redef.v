// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Class#(parameter WIDTH);
    typedef logic [WIDTH-1:0] word;
    typedef struct {
        word w;
    } Struct;
endclass

module t;
   Class#(1)::Struct s1;
   Class#(1)::Struct s2;
   Class#(2)::Struct s3;

   initial begin
      $display("%p", s1);
      $display("%p", s2);
      $display("%p", s3);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
