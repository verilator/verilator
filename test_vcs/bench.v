// DESCRIPTION: Verilator Test: Top level testbench for VCS or other fully Verilog compliant simulators
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

`timescale 1 ns / 1ns

module bench;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [39:0]		out_quad;		// From top of top.v
   wire [1:0]		out_small;		// From top of top.v
   wire [69:0]		out_wide;		// From top of top.v
   wire			passed;			// From top of top.v
   // End of automatics

   reg  clk;
   reg 	       fastclk;
   reg 	       reset_l;
   reg [1:0]   in_small;
   reg [39:0]  in_quad;
   reg [69:0]  in_wide;

   // Test cases
   top top (/*AUTOINST*/
	    // Outputs
	    .passed			(passed),
	    .out_small			(out_small[1:0]),
	    .out_quad			(out_quad[39:0]),
	    .out_wide			(out_wide[69:0]),
	    // Inputs
	    .clk			(clk),
	    .fastclk			(fastclk),
	    .reset_l			(reset_l),
	    .in_small			(in_small[1:0]),
	    .in_quad			(in_quad[39:0]),
	    .in_wide			(in_wide[69:0]));

    //surefire lint_off STMINI
    //surefire lint_off STMFVR
    //surefire lint_off DLYONE

   integer fh;

   // surefire lint_off CWECBB
   initial begin
      reset_l = 1'b1;	// Want to catch negedge
      fastclk = 0;
      clk = 0;
      forever begin
	 in_small = 0;
	 in_wide = 0;
	 $write("[%0t] %x %x %x %x %x\n", $time, clk, reset_l, passed, out_small, out_wide);
	 if (($time % 10) == 3) clk = 1'b1;
	 if (($time % 10) == 8) clk = 1'b0;
	 if ($time>10) reset_l = 1'b1;
	 else if ($time > 1) reset_l = 1'b0;
	 if ($time>60 || passed === 1'b1) begin
	    if (passed !== 1'b1) begin
	       $write("A Test failed!!!\n");
	       $stop;
	    end
	    else begin
	       $write("*-* All Finished *-*\n");  // Magic if using perl's Log::Detect
	       fh = $fopen("test_passed.log");
	       $fclose(fh);
	    end
	    $finish;
	 end
	 #1;
	 fastclk = !fastclk;
      end
   end

endmodule

// Local Variables:
// verilog-library-directories:("." "../test_v")
// compile-command: "vlint --brief -f ../test_v/input.vc bench.v"
// End:
