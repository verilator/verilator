// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   integer 	cyc=0;

   reg [6:0] mem1d;
   reg [6:0] mem2d [5:0];
   reg [6:0] mem3d [4:0][5:0];

   integer   i,j,k;

   // Four different test cases for out of bounds
   //	=
   //	<=
   //   Continuous assigns
   //	Output pin interconnect (also covers cont assigns)
   // Each with both bit selects and array selects

   initial begin
      mem1d[0] = 1'b0;
      i=7;
      mem1d[i] = 1'b1;
      if (mem1d[0] !== 1'b0) $stop;
      //
      for (i=0; i<8; i=i+1) begin
	 for (j=0; j<8; j=j+1) begin
	    for (k=0; k<8; k=k+1) begin
	       mem1d[k] = k[0];
	       mem2d[j][k] = j[0]+k[0];
	       mem3d[i][j][k] = i[0]+j[0]+k[0];
	    end
	 end
      end
      for (i=0; i<5; i=i+1) begin
	 for (j=0; j<6; j=j+1) begin
	    for (k=0; k<7; k=k+1) begin
	       if (mem1d[k] !== k[0]) $stop;
	       if (mem2d[j][k] !== j[0]+k[0]) $stop;
	       if (mem3d[i][j][k] !== i[0]+j[0]+k[0]) $stop;
	    end
	 end
      end
   end

   integer   wi;
   wire [31:0] wd = cyc;
   reg [31:0] reg2d[6:0];
   always @ (posedge clk) reg2d[wi[2:0]] <= wd;

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d reg2d[%0d]=%0x wd=%0x\n",$time, cyc, wi[2:0], reg2d[wi[2:0]], wd);
`endif
      cyc <= cyc + 1;
      if (cyc<10) begin
	 wi <= 0;
      end
      else if (cyc==10) begin
	 wi <= 1;
      end
      else if (cyc==11) begin
	 if (reg2d[0] !== 10) $stop;
	 wi <= 6;
      end
      else if (cyc==12) begin
	 if (reg2d[0] !== 10) $stop;
	 if (reg2d[1] !== 11) $stop;
	 wi <= 7;  // Will be ignored
      end
      else if (cyc==13) begin
	 if (reg2d[0] !== 10) $stop;
	 if (reg2d[1] !== 11) $stop;
	 if (reg2d[6] !== 12) $stop;
      end
      else if (cyc==14) begin
	 if (reg2d[0] !== 10) $stop;
	 if (reg2d[1] !== 11) $stop;
	 if (reg2d[6] !== 12) $stop;
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule
