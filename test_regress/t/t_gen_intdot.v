// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003-2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   integer 	cyc=0;

   wire 	out;
   reg 		in;

   Genit g (.clk(clk), .value(in), .result(out));

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%0d %x %x\n",$time, cyc, in, out);
      cyc <= cyc + 1;
      if (cyc==0) begin
	 // Setup
	 in <= 1'b1;
      end
      else if (cyc==1) begin
	 in <= 1'b0;
      end
      else if (cyc==2) begin
	 if (out != 1'b1) $stop;
      end
      else if (cyc==3) begin
	 if (out != 1'b0) $stop;
      end
      else if (cyc==9) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

//`define WAVES
`ifdef WAVES
   initial begin
      $dumpfile({`STRINGIFY(`TEST_OBJ_DIR),"/simx.vcd"});
      $dumpvars(12, t);
   end
`endif

endmodule

module Generate (clk, value, result);
   input clk;
   input value;
   output result;

   reg Internal;

   assign result = Internal ^ clk;

   always @(posedge clk)
     Internal <= #1 value;
endmodule

module Checker (clk, value);
  input clk, value;

   always @(posedge clk) begin
      $write ("[%0t] value=%h\n", $time, value);
   end

endmodule

module Test (clk, value, result);
   input clk;
   input value;
   output result;

   Generate gen (clk, value, result);
   Checker  chk (clk, gen.Internal);

endmodule

module Genit (clk, value, result);
   input clk;
   input value;
   output result;

`ifndef ATSIM  // else unsupported
 `ifndef NC  // else unsupported
  `define WITH_FOR_GENVAR
 `endif
`endif

`define WITH_GENERATE
`ifdef WITH_GENERATE
 `ifndef WITH_FOR_GENVAR
   genvar i;
 `endif
   generate
      for (
 `ifdef WITH_FOR_GENVAR
	   genvar
 `endif
	   i = 0; i < 1; i = i + 1)
	begin : foo
	   Test tt (clk, value, result);
	end
   endgenerate
`else
   Test tt (clk, value, result);
`endif

   wire Result2 = t.g.foo[0].tt.gen.Internal;  // Works - Do not change!
   always @ (posedge clk) begin
      $write("[%0t] Result2 = %x\n", $time, Result2);
   end

endmodule
