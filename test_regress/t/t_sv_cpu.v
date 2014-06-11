// DESCRIPTION: Verilator: System Verilog test of a complete CPU
//
// This code instantiates and runs a simple CPU written in System Verilog.
//
// This file ONLY is placed into the Public Domain, for any use, without
// warranty.

// Contributed 2012 by M W Lund, Atmel Corporation and Jeremy Bennett, Embecosm.


module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   /*AUTOWIRE*/

   // **************************************************************************
   // Regs and Wires
   // **************************************************************************

   reg 	   rst;
   integer rst_count;
   integer clk_count;


   testbench testbench_i (/*AUTOINST*/
			  // Inputs
			  .clk			(clk),
			  .rst			(rst));


   // **************************************************************************
   // Reset Generation
   // **************************************************************************

   initial begin
      rst       = 1'b1;
      rst_count = 0;
   end

   always @( posedge clk ) begin
      if (rst_count < 2) begin
	 rst_count++;
      end
      else begin
	 rst = 1'b0;
      end
   end


   // **************************************************************************
   // Drive simulation for 500 clock cycles
   // **************************************************************************

   initial begin
`ifdef TEST_VERBOSE
      $display( "[testbench] - Start of simulation ----------------------- " );
`endif
      clk_count = 0;
   end

   always @( posedge clk ) begin
      if (90 == clk_count) begin
	 $finish ();
      end
      else begin
	 clk_count++;
      end
   end

   final begin
`ifdef TEST_VERBOSE
      $display( "[testbench] - End of simulation ------------------------- " );
`endif
      $write("*-* All Finished *-*\n");
   end


endmodule


module testbench (/*AUTOARG*/
   // Inputs
   clk, rst
   );

   input  clk;
   input  rst;

   // **************************************************************************
   // Local parameters
   // **************************************************************************

   localparam
     NUMPADS = $size( pinout );


   // **************************************************************************
   // Regs and Wires
   // **************************************************************************

   // **** Pinout ****
`ifdef VERILATOR  // see t_tri_array
   wire   [NUMPADS:1] pad;    // GPIO Pads (PORT{A,...,R}).
`else
   wire  pad [1:NUMPADS];    // GPIO Pads (PORT{A,...,R}).
`endif


   // **************************************************************************
   // Regs and Wires, Automatics
   // **************************************************************************

   /*AUTOWIRE*/


   // **************************************************************************
   // Includes (Testbench extensions)
   // **************************************************************************

   // N/A


   // **************************************************************************
   // Chip Instance
   // **************************************************************************

   chip
     i_chip
       (
        /*AUTOINST*/
	// Inouts
	.pad				(pad[NUMPADS:1]),
	// Inputs
	.clk				(clk),
	.rst				(rst));


endmodule // test

// Local Variables:
// verilog-library-directories:("." "t_sv_cpu_code")
// End:
