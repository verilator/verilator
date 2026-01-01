// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class ParamClass #(string P = "ABC", R = "GDF");
endclass

module t #(
   parameter int A = 0, B = 1, C = 2, type D = int, E = string, F =
      struct packed {
         struct packed {
            logic a;
         } b;
      }
);
   parameter bit G = 1'b0, H = 1'b1;
   parameter type I = int, J = string;
   E str1 = "abc";
   J str2 = "";

   F struct1;
   assign struct1.b.a = 1'b1;

   initial begin
      automatic ParamClass param_class = new;
      if ($typename(B) != "int") $stop;
      if ($typename(C) != "int") $stop;
      if (str1.len() != 3) $stop;
      if ($typename(H) != "bit") $stop;
      if (str2.len() != 0) $stop;
      if ($typename(param_class.R) != "string") $stop;
      if ($typename(struct1.b.a) != "MEMBERDTYPE 'a'") $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
