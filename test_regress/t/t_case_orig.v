// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   reg 	 _ranit;

   reg 	 rnd;
   reg [2:0] a;
   reg [2:0] b;
   reg [31:0] wide;

   // surefire lint_off STMINI
   initial _ranit = 0;

   wire   sigone1 = 1'b1;
   wire   sigone2 = 1'b1;
   reg 	  ok;

   parameter [1:0] twounkn = 2'b?;  // This gets extended to 2'b??

   // Large case statements should be well optimizable.
   reg [2:0] 	   anot;
   always @ (/*AS*/a) begin
      casez (a)
	default: anot = 3'b001;
	3'd0: anot = 3'b111;
	3'd1: anot = 3'b110;
	3'd2: anot = 3'b101;
	3'd3: anot = 3'b101;
	3'd4: anot = 3'b011;
	3'd5: anot = 3'b010;
	3'd6: anot = 3'b001;	// Same so folds with 7
      endcase
   end

   always @ (posedge clk) begin
      if (!_ranit) begin
	 _ranit <= 1;
	 rnd <= 1;
	 $write("[%0t] t_case: Running\n", $time);
	 //
	 a = 3'b101;
	 b = 3'b111;
	 // verilator lint_off CASEX
	 casex (a)
	   default: $stop;
	   3'bx1x: $stop;
	   3'b100: $stop;
	   3'bx01: ;
	 endcase
	 casez (a)
	   default: $stop;
	   3'b?1?: $stop;
	   3'b100: $stop;
	   3'b?01: ;
	 endcase
	 casez (a)
	   default: $stop;
	   {1'b0, twounkn}: $stop;
	   {1'b1, twounkn}: ;
	 endcase
	 casez (b)
	   default: $stop;
	   {1'b0, twounkn}: $stop;
	   {1'b1, twounkn}: ;
//	   {1'b0, 2'b??}: $stop;
//	   {1'b1, 2'b??}: ;
	 endcase
	 case(a[0])
	   default: ;
	 endcase
	 casex(a)
	   default: ;
	   3'b?0?: ;
	 endcase
	 // verilator lint_off CASEX
	 //This is illegal, the default occurs before the statements.
	 //case(a[0])
	 //  default: $stop;
	 //  1'b1: ;
	 //endcase
	 //
	 wide = 32'h12345678;
	 casez (wide)
	   default: $stop;
	   32'h12345677,
	   32'h12345678,
	   32'h12345679: ;
	 endcase
	 //
	 ok = 0;
	 casez ({sigone1,sigone2})
	   //2'b10, 2'b01, 2'bXX: ;	// verilator bails at this since in 2 state it can be true...
	   2'b10, 2'b01: ;
	   2'b00: ;
	   default: ok=1'b1;
	 endcase
         if (ok !== 1'b1) $stop;
	 //

	 if (rnd) begin
	    $write("");
	 end
	 //
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

   // Check parameters in case statements
   parameter ALU_DO_REGISTER		= 3'h1;  // input selected by reg addr.
   parameter DSP_REGISTER_V		= 6'h03;

   reg [2:0] alu_ctl_2s;	// Delayed version of alu_ctl
   reg [5:0] reg_addr_2s;	// Delayed version of reg_addr
   reg [7:0] ir_slave_2s;	// Instruction Register delayed 2 phases
   reg [15:10] f_tmp_2s;	// Delayed copy of F
   reg 	      p00_2s;

   initial begin
      alu_ctl_2s = 3'h1;
      reg_addr_2s = 6'h3;
      ir_slave_2s= 0;
      f_tmp_2s= 0;
      casex ({alu_ctl_2s,reg_addr_2s,
	      ir_slave_2s[7],ir_slave_2s[5:4],ir_slave_2s[1:0],
	      f_tmp_2s[11:10]})
	default:  p00_2s = 1'b0;
	{ALU_DO_REGISTER,DSP_REGISTER_V,1'bx,2'bx,2'bx,2'bx}: p00_2s = 1'b1;
      endcase
      if (1'b0) $display ("%x %x %x %x", alu_ctl_2s, ir_slave_2s, f_tmp_2s, p00_2s); //Prevent unused
      //
      case ({1'b1, 1'b1})
	default: $stop;
	{1'b1, p00_2s}: ;
      endcase
   end

   // Check wide overlapping cases
   // surefire lint_off CSEOVR
   parameter ANY_STATE = 7'h??;
   reg [19:0] foo;
   initial begin
      foo = {1'b0,1'b0,1'b0,1'b0,1'b0,7'h04,8'b0};
      casez (foo)
	default: $stop;
	{1'b1,1'b?,1'b?,1'b?,1'b?,ANY_STATE,8'b?}:  $stop;
	{1'b?,1'b1,1'b?,1'b?,1'b?,7'h00,8'b?}: $stop;
	{1'b?,1'b?,1'b1,1'b?,1'b?,7'h00,8'b?}: $stop;
	{1'b?,1'b?,1'b?,1'b1,1'b?,7'h00,8'b?}: $stop;
	{1'b?,1'b?,1'b?,1'b?,1'b?,7'h04,8'b?}: ;
	{1'b?,1'b?,1'b?,1'b?,1'b?,7'h06,8'hdf}: $stop;
	{1'b?,1'b?,1'b?,1'b?,1'b?,7'h06,8'h00}: $stop;
      endcase
   end
   initial begin
      foo = 20'b1010;
      casex (foo[3:0])
	default: $stop;
	4'b0xxx,
	4'b100x,
	4'b11xx: $stop;
	4'b1010: ;
      endcase
   end
   initial begin
      foo = 20'b1010;
      ok = 1'b0;
      // Test of RANGE(CONCAT reductions...
      casex ({foo[3:2],foo[1:0],foo[3]})
	5'bxx10x: begin ok=1'b0; foo=20'd1; ok=1'b1; end  // Check multiple expressions
	5'bxx00x: $stop;
	5'bxx01x: $stop;
	5'bxx11x: $stop;
      endcase
      if (!ok) $stop;
   end

endmodule
