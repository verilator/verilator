// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Class1 #(type T);
  typedef T::Some_type2 Some_type1;
endclass

class Class2;
  typedef int Some_type2;
endclass



module t;
   initial begin
      Class1#(Class2)::Some_type1 value1 = 7;
      // TODO: uncomment those lines when `type` will be fixed
      // type(value1) in this case causes an error:
      //  %Error: Internal Error: t/t_typedef_param_class.v:19:16:
      // ../V3Ast.h:2659: AstNode is not of expected type, but instead has type 'VARREF'
      //     19 |       if (type(value1) != type(value2)) $stop;
      // int value2 = 13;
      // if (type(value1) != type(value2)) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
