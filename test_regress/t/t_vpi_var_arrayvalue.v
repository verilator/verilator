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
import "DPI-C" context function int mon_check();
`endif

module t (/*AUTOARG*/
   // Outputs
   // Inputs
   clk
   );

`ifdef VERILATOR
`systemc_header
extern "C" int mon_check();
`verilog
`endif


/*-------------------------------------------
VARIABLE DEFINITIONS
-------------------------------------------*/
   //overhead
   input clk;
   integer status;
   reg [31:0] count;
   reg c_tests_done, v_tests_done;

   //mon_check_bad
   logic      bad [0:0] /*verilator public_flat_rw */;
   localparam bad_param /*verilator public_flat_rw */ = 1;

/*-------------------------------------------
TICK COUNTER
-------------------------------------------*/
   always @(posedge clk) begin
      count <= count + 2;
      if (count == 1000) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

/*-------------------------------------------
C TEST SUITE
-------------------------------------------*/
   initial begin
      c_tests_done = 0;
      v_tests_done = 0;
`ifdef VERILATOR
      status = $c32("mon_check()");
`endif
`ifdef IVERILOG
      status = $mon_check();
`endif
`ifndef USE_VPI_NOT_DPI
      status = mon_check();
`endif
      if (status!=0) begin
         $write("%%Error: t_vpi_var_arrayvalue.cpp:%0d: C Test failed\n", status);
         $stop;
      end
      c_tests_done = 1;
   end

/*-------------------------------------------
VERILOG TEST SUITE
-------------------------------------------*/
   always @(posedge clk) begin
      if(c_tests_done && ~v_tests_done) begin
         $write("%%Info: Checking results\n");
         //insert tests here
         v_tests_done <= 1;
      end
   end

endmodule : t
