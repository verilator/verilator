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

`ifdef VERILATOR_COMMENTS
 `define PUBLIC_FLAT_RD /*verilator public_flat_rd*/
 `define PUBLIC_FLAT_RW /*verilator public_flat_rw @(posedge clk)*/
`else
 `define PUBLIC_FLAT_RD
 `define PUBLIC_FLAT_RW
`endif

module t (/*AUTOARG*/
   // Inputs
   input clk                            `PUBLIC_FLAT_RD,

   // test ports
   input  [15:0]        testin          `PUBLIC_FLAT_RD,
   output [23:0]        testout     `PUBLIC_FLAT_RW

   );

`ifdef VERILATOR
`systemc_header
extern "C" int mon_check();
`verilog
`endif

   reg          onebit          `PUBLIC_FLAT_RW;
   reg [2:1]    twoone          `PUBLIC_FLAT_RW;
   reg          onetwo [1:2]    `PUBLIC_FLAT_RW;
   reg [2:1]    fourthreetwoone[4:3] `PUBLIC_FLAT_RW;

   integer      status;

`ifdef iverilog
   // stop icarus optimizing signals away
   wire 	redundant = onebit | onetwo[1] | twoone | fourthreetwoone[3];
`endif

   wire         subin  `PUBLIC_FLAT_RD;
   wire         subout `PUBLIC_FLAT_RD;
   sub sub(.*);

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
	 $write("%%Error: t_vpi_var.cpp:%0d: C Test failed\n", status);
	 $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule : t

module sub (
   input  subin  `PUBLIC_FLAT_RD,
   output subout `PUBLIC_FLAT_RD
);
endmodule : sub
