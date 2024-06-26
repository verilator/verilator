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

   //_mon_check_get_bad
   logic      [7:0] bad_dim1                 /*verilator public_flat_rw */;
   logic      [7:0] bad_dim2 [0:1]           /*verilator public_flat_rw */;
   logic      [7:0] bad_dim3 [0:1][0:1]      /*verilator public_flat_rw */;
   localparam bad_param /*verilator public_flat_rw */ = 1;

   //_mon_check_get_vector
   logic      [7:0] int_dim2_8 [0:1][0:2] /*verilator public_flat_rw */;
   assign int_dim2_8[0][0] = 8'h80;
   assign int_dim2_8[0][1] = 8'h81;
   assign int_dim2_8[0][2] = 8'h82;
   assign int_dim2_8[1][0] = 8'h83;
   assign int_dim2_8[1][1] = 8'h84;
   assign int_dim2_8[1][2] = 8'h85;

   logic      [15:0] int_dim2_16 [0:1][0:2] /*verilator public_flat_rw */;
   assign int_dim2_16[0][0] = 16'h8000;
   assign int_dim2_16[0][1] = 16'h8001;
   assign int_dim2_16[0][2] = 16'h8002;
   assign int_dim2_16[1][0] = 16'h8003;
   assign int_dim2_16[1][1] = 16'h8004;
   assign int_dim2_16[1][2] = 16'h8005;

   logic      [31:0] int_dim2_32 [0:1][0:2] /*verilator public_flat_rw */;
   assign int_dim2_32[0][0] = 32'h80000000;
   assign int_dim2_32[0][1] = 32'h80000001;
   assign int_dim2_32[0][2] = 32'h80000002;
   assign int_dim2_32[1][0] = 32'h80000003;
   assign int_dim2_32[1][1] = 32'h80000004;
   assign int_dim2_32[1][2] = 32'h80000005;

   //_mon_check_get_real
   real   real_dim2 [0:1][0:2] /*verilator public_flat_rw */;
   assign real_dim2[0][0] = 0.5;
   assign real_dim2[0][1] = 1.5;
   assign real_dim2[0][2] = 2.5;
   assign real_dim2[1][0] = 3.5;
   assign real_dim2[1][1] = 4.5;
   assign real_dim2[1][2] = 5.5;

   //_mon_check_get_vector
   logic      [7:0] vector_dim2_8 [0:1][0:2] /*verilator public_flat_rw */;
   assign vector_dim2_8[0][0] = 8'h80;
   assign vector_dim2_8[0][1] = 8'h81;
   assign vector_dim2_8[0][2] = 8'h82;
   assign vector_dim2_8[1][0] = 8'h83;
   assign vector_dim2_8[1][1] = 8'h84;
   assign vector_dim2_8[1][2] = 8'h85;

   logic      [15:0] vector_dim2_16 [0:1][0:2] /*verilator public_flat_rw */;
   assign vector_dim2_16[0][0] = 16'h8000;
   assign vector_dim2_16[0][1] = 16'h8001;
   assign vector_dim2_16[0][2] = 16'h8002;
   assign vector_dim2_16[1][0] = 16'h8003;
   assign vector_dim2_16[1][1] = 16'h8004;
   assign vector_dim2_16[1][2] = 16'h8005;

   logic      [31:0] vector_dim2_32 [0:1][0:2] /*verilator public_flat_rw */;
   assign vector_dim2_32[0][0] = 32'h80000000;
   assign vector_dim2_32[0][1] = 32'h80000001;
   assign vector_dim2_32[0][2] = 32'h80000002;
   assign vector_dim2_32[1][0] = 32'h80000003;
   assign vector_dim2_32[1][1] = 32'h80000004;
   assign vector_dim2_32[1][2] = 32'h80000005;

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
