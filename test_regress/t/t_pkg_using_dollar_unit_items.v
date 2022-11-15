// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

typedef int my_type;

class my_class;
   static int a = 1;
endclass

function int get_val;
   return 2;
endfunction

package my_pkg;
   int      my_type_size = $bits(my_type);
   int      my_class_a = my_class::a;
   int      get_val_result = get_val();
endpackage

package overwriting_pkg;
   typedef logic [9:0] my_type;

   class my_class;
      static int a = 2;
   endclass

   function int get_val;
      return 3;
   endfunction

   int      my_type_size = $bits(my_type);
   int      my_class_a = my_class::a;
   int      get_val_result = get_val();
endpackage

module t (/*AUTOARG*/
      clk
   );

   input clk;

   always @(posedge clk) begin
      bit [5:0] results = {my_pkg::my_type_size == 32,
                           my_pkg::my_class_a == 1,
                           my_pkg::get_val_result == 2,
                           overwriting_pkg::my_type_size == 10,
                           overwriting_pkg::my_class_a == 2,
                           overwriting_pkg::get_val_result == 3};

      if (results == '1) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("Results: %b\n", results);
         $stop;
      end
   end
endmodule
