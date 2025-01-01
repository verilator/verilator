// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

typedef int my_type;

class my_class;
   static int a = 1;
endclass

function int get_val;
   return 2;
endfunction

package my_pkg;
   int my_type_size = $bits(my_type);
   int my_class_a = my_class::a;
   int get_val_result = get_val();
endpackage

package overwriting_pkg;
   typedef logic [9:0] my_type;

   class my_class;
      static int a = 2;
   endclass

   function int get_val;
      return 3;
   endfunction

   int my_type_size = $bits(my_type);
   int my_class_a = my_class::a;
   int get_val_result = get_val();
endpackage

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int cyc;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 2) begin
         `checkh(my_pkg::my_type_size, 32);
         `checkh(my_pkg::my_class_a, 1);
         `checkh(my_pkg::get_val_result, 2);
         `checkh(overwriting_pkg::my_type_size, 10);
         `checkh(overwriting_pkg::my_class_a, 2);
         `checkh(overwriting_pkg::get_val_result, 3);
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
