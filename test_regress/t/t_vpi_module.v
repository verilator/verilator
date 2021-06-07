// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`ifndef IVERILOG
import "DPI-C" context function int mon_check();
`endif

package somepackage;
   int someint /*verilator public_flat_rw*/;
endpackage

module t (/*AUTOARG*/
   // Inputs
   clk
   );

`ifdef USE_DOLLAR_C32
`systemc_header
extern "C" int mon_check();
`verilog
`endif

   input clk;

   integer        status;

   wire           a, b, x;

   A mod_a(/*AUTOINST*/
           // Outputs
           .x                           (x),
           // Inputs
           .clk                         (clk),
           .a                           (a),
           .b                           (b));

   // Test loop
   initial begin
`ifdef IVERILOG
      status = $mon_check();
`elsif USE_DOLLAR_C32
      status = $c32("mon_check()");
`else
      status = mon_check();
`endif
      if (status!=0) begin
         $write("%%Error: t_vpi_module.cpp:%0d: C Test failed\n", status);
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule : t

module A(/*AUTOARG*/
   // Outputs
   x,
   // Inputs
   clk, a, b
   );

   input clk;

   input a, b;
   output x;

   wire   y, c;

   B mod_b(/*AUTOINST*/
           // Outputs
           .y                           (y),
           // Inputs
           .b                           (b),
           .c                           (c));

   C \mod_c. (/*AUTOINST*/
           // Outputs
           .x                           (x),
           // Inputs
           .clk                         (clk),
           .a                           (a),
           .y                           (y));

endmodule : A

module B(/*AUTOARG*/
   // Outputs
   y,
   // Inputs
   b, c
   ); /*verilator public_module*/
   input b, c;

   output reg y;

   always @(*) begin : myproc
      y = b ^ c;
   end

endmodule

module C(/*AUTOARG*/
   // Outputs
   x,
   // Inputs
   clk, a, y
   );

   input clk;

   input a, y;

   output reg x /* verilator public_flat_rw */;

   always @(posedge clk) begin
     x <= a & y;
   end

endmodule
