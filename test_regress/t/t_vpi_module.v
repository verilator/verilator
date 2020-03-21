// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`ifdef USE_VPI_NOT_DPI
//We call it via $c so we can verify DPI isn't required - see bug572
`else
import "DPI-C" context function integer mon_check();
`endif

module t (/*AUTOARG*/
   // Inputs
   clk
   );

`ifdef VERILATOR
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
`ifdef VERILATOR
      status = $c32("mon_check()");
`endif
`ifdef iverilog
     status = $mon_check();
`endif
`ifndef USE_VPI_NOT_DPI
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
