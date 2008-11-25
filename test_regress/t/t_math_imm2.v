// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.
//
// Example module to create problem.
//
//    generate a 64 bit value with bits
//      [HighMaskSel_Bot   : LowMaskSel_Bot   ] = 1
//      [HighMaskSel_Top+32: LowMaskSel_Top+32] = 1
//    all other bits zero.

module t_math_imm2 (/*AUTOARG*/
   // Outputs
   LogicImm, LowLogicImm, HighLogicImm,
   // Inputs
   LowMaskSel_Top, HighMaskSel_Top, LowMaskSel_Bot, HighMaskSel_Bot
   );
   input  [4:0]  LowMaskSel_Top, HighMaskSel_Top;
   input [4:0] 	 LowMaskSel_Bot, HighMaskSel_Bot;
   output [63:0] LogicImm;

   output [63:0] LowLogicImm, HighLogicImm;

   /* verilator lint_off UNSIGNED */
   /* verilator lint_off CMPCONST */
   genvar 	 i;
   generate
      for (i=0;i<64;i=i+1) begin : MaskVal
	 if (i >= 32) begin
	    assign LowLogicImm[i]  = (LowMaskSel_Top <= i[4:0]);
	    assign HighLogicImm[i] = (HighMaskSel_Top >= i[4:0]);
	 end
	 else begin
	    assign LowLogicImm[i]  = (LowMaskSel_Bot <= i[4:0]);
	    assign HighLogicImm[i] = (HighMaskSel_Bot >= i[4:0]);
	 end
      end
   endgenerate

   assign LogicImm = LowLogicImm & HighLogicImm;
endmodule
