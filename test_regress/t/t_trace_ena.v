// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc=1;
   // verilator tracing_off
   integer b_trace_off;
   // verilator tracing_on
   integer c_trace_on;
   real	   r;

   // verilator tracing_off
   sub sub ();
   // verilator tracing_on

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 b_trace_off <= cyc;
	 c_trace_on <= b_trace_off;
	 r <= r + 0.1;
	 if (cyc==4) begin
	    if (c_trace_on != 2) $stop;
	 end
	 if (cyc==10) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule

module sub;
   integer inside_sub = 0;
endmodule
