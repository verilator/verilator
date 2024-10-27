// DESCRIPTION: Verilator: Demonstrate struct literal param assignment problem
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package Some_pkg;
    typedef struct packed {
        int foo;
    } some_struct_t;
endpackage

module sub #(
    parameter Some_pkg::some_struct_t the_some_struct
) ();
endmodule

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // finish report
   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

   sub #(
       .the_some_struct(
            Some_pkg::some_struct_t'{
                foo: 1
            }))
    the_sub ();

endmodule
