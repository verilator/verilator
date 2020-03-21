// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // verilator lint_off BLKANDNBLK
   // verilator lint_off COMBDLY
   // verilator lint_off UNOPT
   // verilator lint_off UNOPTFLAT
   // verilator lint_off MULTIDRIVEN

   reg [31:0] 	 runnerm1, runner; initial runner = 0;
   reg [31:0] 	 runcount; initial runcount = 0;
   reg [31:0] 	 clkrun; initial clkrun = 0;
   reg [31:0] 	 clkcount; initial clkcount = 0;
   always @ (/*AS*/runner) begin
      runnerm1 = runner - 32'd1;
   end
   reg run0;
   always @ (/*AS*/runnerm1) begin
      if ((runner & 32'hf)!=0) begin
	 runcount = runcount + 1;
	 runner = runnerm1;
	 $write ("     seq runcount=%0d  runner =%0x\n",runcount, runnerm1);
      end
      run0 = (runner[8:4]!=0 && runner[3:0]==0);
   end

   always @ (posedge run0) begin
      // Do something that forces another combo run
      clkcount <= clkcount + 1;
      runner[8:4] <= runner[8:4] - 1;
      runner[3:0] <= 3;
      $write ("[%0t]   posedge runner=%0x\n", $time, runner);
   end

   reg [7:0] cyc; initial cyc=0;
   always @ (posedge clk) begin
      $write("[%0t] %x  counts %0x %0x\n",$time,cyc,runcount,clkcount);
      cyc <= cyc + 8'd1;
      case (cyc)
	8'd00: begin
	   runner <= 0;
	end
	8'd01: begin
	   runner <= 32'h35;
	end
	default: ;
      endcase
      case (cyc)
	8'd02: begin
	   if (runcount!=32'he) $stop;
	   if (clkcount!=32'h3) $stop;
	end
	8'd03: begin
	   $write("*-* All Finished *-*\n");
	   $finish;
	end
	default: ;
      endcase
   end
endmodule
