// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.

`begin_keywords "VAMS-2.3"

module t (/*autoarg*/
   // Outputs
   aout,
   // Inputs
   clk, in
   );

   input clk;

   input [15:0] in;
   output 	aout; 
   wreal aout;

   integer 	cyc=0;

   real vin;
   real gnd;
   wire 	out;
   within_range within_range (/*AUTOINST*/
			      // Interfaces
			      .vin		(vin),
			      .gnd		(gnd),
			      // Outputs
			      .out		(out));

   parameter real lsb = 1;
   // verilator lint_off WIDTH
   assign  aout = $itor(in) * lsb;
   // verilator lint_on WIDTH

   always @ (posedge clk) begin
      cyc <= cyc + 1;
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d aout=%d (%f-%f=%f)\n",$time, cyc, out, vin, gnd, within_range.in_int);
`endif
      if (cyc==0) begin
	 // Setup
	 gnd = 0.0;
	 vin = 0.2;
      end
      else if (cyc==2) begin
	 if (out != 0) $stop;
      end
      else if (cyc==3) begin
	 gnd = 0.0;
	 vin = 0.6;
      end
      else if (cyc==4) begin
	 if (out != 1) $stop;
      end
      else if (cyc==5) begin
	 gnd = 0.6;
	 vin = 0.8;
      end
      else if (cyc==6) begin
	 if (out != 0) $stop;
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module within_range
  (input wreal vin,
   input wreal gnd,
   output out);

   parameter real V_MIN = 0.5;
   parameter real V_MAX = 10;

   wreal in_int = vin - gnd;
   wire out = (V_MIN <= in_int && in_int <= V_MAX);
endmodule
