// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
// Example module to create problem.
//
//    generate a 64 bit value with bits
//      [HighMaskSel_Bot   : LowMaskSel_Bot   ] = 1
//      [HighMaskSel_Top+32: LowMaskSel_Top+32] = 1
//    all other bits zero.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=0;
   reg [7:0] crc;
   reg [63:0] sum;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [63:0]		HighLogicImm;		// From example of example.v
   wire [63:0]		LogicImm;		// From example of example.v
   wire [63:0]		LowLogicImm;		// From example of example.v
   // End of automatics

   wire [5:0]   LowMaskSel_Top  = crc[5:0];
   wire [5:0]   LowMaskSel_Bot  = crc[5:0];
   wire [5:0]   HighMaskSel_Top = crc[5:0]+{4'b0,crc[7:6]};
   wire [5:0]   HighMaskSel_Bot = crc[5:0]+{4'b0,crc[7:6]};

   example example (/*AUTOINST*/
		    // Outputs
		    .LogicImm		(LogicImm[63:0]),
		    .LowLogicImm	(LowLogicImm[63:0]),
		    .HighLogicImm	(HighLogicImm[63:0]),
		    // Inputs
		    .LowMaskSel_Top	(LowMaskSel_Top[5:0]),
		    .HighMaskSel_Top	(HighMaskSel_Top[5:0]),
		    .LowMaskSel_Bot	(LowMaskSel_Bot[5:0]),
		    .HighMaskSel_Bot	(HighMaskSel_Bot[5:0]));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      crc <= {crc[6:0], ~^ {crc[7],crc[5],crc[4],crc[3]}};
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%b %d.%d,%d.%d -> %x.%x -> %x\n",$time, cyc, crc,
	     LowMaskSel_Top, HighMaskSel_Top, LowMaskSel_Bot, HighMaskSel_Bot,
	     LowLogicImm, HighLogicImm, LogicImm);
`endif
      if (cyc==0) begin
	 // Single case
	 crc <= 8'h0;
	 sum <= 64'h0;
      end
      else if (cyc==1) begin
	 // Setup
	 crc <= 8'hed;
	 sum <= 64'h0;
      end
      else if (cyc<90) begin
	 sum <= {sum[62:0],sum[63]} ^ LogicImm;
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%b %x\n",$time, cyc, crc, sum);
	 if (crc !== 8'b00111000) $stop;
	 if (sum !== 64'h58743ffa61e41075) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module example (/*AUTOARG*/
   // Outputs
   LogicImm, LowLogicImm, HighLogicImm,
   // Inputs
   LowMaskSel_Top, HighMaskSel_Top, LowMaskSel_Bot, HighMaskSel_Bot
   );

   input  [5:0]  LowMaskSel_Top, HighMaskSel_Top;
   input [5:0] 	 LowMaskSel_Bot, HighMaskSel_Bot;
   output [63:0] LogicImm;

   output [63:0] 	 LowLogicImm, HighLogicImm;


   wire [63:0] 	 LowLogicImm, HighLogicImm;

   /* verilator lint_off UNSIGNED */
   /* verilator lint_off CMPCONST */
   genvar 	 i;
   generate
      for (i=0;i<64;i=i+1) begin : MaskVal
	 if (i >= 32) begin
	    assign LowLogicImm[i]  = (LowMaskSel_Top <= i[5:0]);
	    assign HighLogicImm[i] = (HighMaskSel_Top >= i[5:0]);
	 end
	 else begin
	    assign LowLogicImm[i]  = (LowMaskSel_Bot <= i[5:0]);
	    assign HighLogicImm[i] = (HighMaskSel_Bot >= i[5:0]);
	 end
      end
   endgenerate
   /* verilator lint_on UNSIGNED */
   /* verilator lint_on CMPCONST */

   assign LogicImm = LowLogicImm & HighLogicImm;
endmodule
