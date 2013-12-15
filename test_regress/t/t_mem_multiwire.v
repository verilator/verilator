// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // verilator lint_off LITENDIAN
   wire [7:0] array [2:0][1:3];
   wire [7:0] arrayNoColon [2][3];
   // verilator lint_on LITENDIAN

   integer cyc; initial cyc=0;
   integer    i0,i1,i2;
   genvar     g0,g1,g2;

   generate
      for (g0=0; g0<3; g0=g0+1) begin
	 for (g1=1; g1<4; g1=g1+1) begin
	    inst inst (.q(array[g0[1:0]] [g1[1:0]]),
		       .cyc(cyc),
		       .i0(g0[1:0]),
		       .i1(g1[1:0]));
	 end
      end
   endgenerate

   always @ (posedge clk) begin
      //$write("cyc==%0d\n",cyc);
      cyc <= cyc + 1;
      if (cyc==2) begin
	 if (array[2][1] !== 8'h92) $stop;
	 for (i0=0; i0<3; i0=i0+1) begin
	    for (i1=1; i1<4; i1=i1+1) begin
	       //$write("  array[%0d][%0d] == 8'h%x\n",i0,i1,array[i0[1:0]] [i1[1:0]]);
	       if (array[i0[1:0]] [i1[1:0]] != {i0[1:0], i1[1:0], cyc[3:0]}) $stop;
	    end
	 end
      end
      else if (cyc==9) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module inst (/*AUTOARG*/
   // Outputs
   q,
   // Inputs
   cyc, i0, i1
   );
   output reg [7:0] q;
   input [31:0] cyc;
   input [1:0] 	i0;
   input [1:0] 	i1;

   inst2 inst2 (/*AUTOINST*/
		// Inputs
		.cyc			(cyc[31:0]),
		.i0			(i0[1:0]),
		.i1			(i1[1:0]));

   always @* begin
      q = {i0, i1, cyc[3:0]};
   end
endmodule

module inst2 (/*AUTOARG*/
   // Inputs
   cyc, i0, i1
   );
   /*verilator no_inline_module*/   // So we'll get a CELL under a GENFOR, without inlining
   input [31:0] cyc;
   input [1:0] 	i0;
   input [1:0] 	i1;
   initial begin
      if (cyc==32'h1) $write("[%0t] i0=%d i1=%d\n", $time, i0, i1);
   end
endmodule
