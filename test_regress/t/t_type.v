// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   real x;
   real y;
   var type(x+y) z;
   localparam type x_type = type(x);
   x_type value;

   initial begin
      value = 1.234;
      if (value != 1.234) $stop();
      x = 1.2;
      y = 2.3;
      z = x + y;
      if (z != (1.2+2.3)) $stop;
      z = type(z)'(22);
      if (z != 22.0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

   localparam type x_minus_y_type = type(x-y);
   sub_real #(.the_type (x_minus_y_type)) the_sub_real_1();
   sub_real #(.the_type (type(x-y))) the_sub_real_2();
   localparam type type1 = type(x*y);
   type1 type1_var;
   localparam type type2 = type(type1_var/y);
   sub_real #(.the_type (type2)) the_sub_real_3();

endmodule

module sub_real #(
    parameter type the_type = bit
) ();
    the_type the_value;

    initial begin
        the_value = 4.567;
        if (the_value != 4.567) $stop();
    end
endmodule
