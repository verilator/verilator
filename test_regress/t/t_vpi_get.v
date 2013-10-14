// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.

`ifdef USE_VPI_NOT_DPI
//We call it via $c so we can verify DPI isn't required - see bug572
`else
import "DPI-C" context function integer mon_check();
`endif

module t (/*AUTOARG*/
   // Inputs
   input clk                          	/*verilator public_flat_rd		  */,

   // test ports
   input  [15:0] 	testin  	/*verilator public_flat_rd		  */,
   output [23:0] 	testout 	/*verilator public_flat_rw @(posedge clk) */

   );

`ifdef VERILATOR
`systemc_header
extern "C" int mon_check();
`verilog
`endif

   reg		onebit		/*verilator public_flat_rw @(posedge clk) */;
   reg [2:1]	twoone		/*verilator public_flat_rw @(posedge clk) */;
   reg   	onetwo [1:2]	/*verilator public_flat_rw @(posedge clk) */;
   reg [2:1] 	fourthreetwoone[4:3] /*verilator public_flat_rw @(posedge clk) */;

   integer      status;

`ifdef iverilog
   // stop icarus optimizing signals away
   wire 	redundant = onebit | onetwo[1] | twoone | fourthreetwoone[3];
`endif

   wire         subin  /*verilator public_flat_rd*/;
   wire         subout /*verilator public_flat_rd*/;
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
   input  subin  /*verilator public_flat_rd*/,
   output subout /*verilator public_flat_rd*/
);
endmodule : sub
