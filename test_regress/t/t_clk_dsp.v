// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // verilator lint_off GENCLK

   reg [7:0] cyc; initial cyc=0;
   reg [7:0] padd;
   reg 	     dsp_ph1, dsp_ph2, dsp_reset;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [7:0]		out;			// From dspchip of t_dspchip.v
   // End of automatics

   t_dspchip dspchip (/*AUTOINST*/
		      // Outputs
		      .out		(out[7:0]),
		      // Inputs
		      .dsp_ph1		(dsp_ph1),
		      .dsp_ph2		(dsp_ph2),
		      .dsp_reset	(dsp_reset),
		      .padd		(padd[7:0]));

   always @ (posedge clk) begin
      $write("cyc %d\n",cyc);
      if (cyc == 8'd0) begin
	 cyc <= 8'd1;
	 dsp_reset <= 0;	// Need a posedge
	 padd <= 0;
      end
      else if (cyc == 8'd20) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
      else begin
	 cyc <= cyc + 8'd1;
	 dsp_ph1 <= ((cyc&8'd3) == 8'd0);
	 dsp_ph2 <= ((cyc&8'd3) == 8'd2);
	 dsp_reset <= (cyc == 8'd1);
	 padd <= cyc;
	 //$write("[%0t] cyc %d  %x->%x\n", $time, cyc, padd, out);
	 case (cyc)
	   default: $stop;
	   8'd01: ;
	   8'd02: ;
	   8'd03: ;
	   8'd04: ;
	   8'd05: ;
	   8'd06: ;
	   8'd07: ;
	   8'd08: ;
	   8'd09: if (out!==8'h04) $stop;
	   8'd10: if (out!==8'h04) $stop;
	   8'd11: if (out!==8'h08) $stop;
	   8'd12: if (out!==8'h08) $stop;
	   8'd13: if (out!==8'h00) $stop;
	   8'd14: if (out!==8'h00) $stop;
	   8'd15: if (out!==8'h00) $stop;
	   8'd16: if (out!==8'h00) $stop;
	   8'd17: if (out!==8'h0c) $stop;
	   8'd18: if (out!==8'h0c) $stop;
	   8'd19: if (out!==8'h10) $stop;
	 endcase
      end
   end

endmodule

module t_dspchip (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   dsp_ph1, dsp_ph2, dsp_reset, padd
   );
   input dsp_ph1, dsp_ph2, dsp_reset;
   input [7:0] padd;
   output [7:0] out;

   wire 	dsp_ph1, dsp_ph2;
   wire [7:0] 	out;
   wire 	pla_ph1, pla_ph2;
   wire 	out1_r;
   wire [7:0] 	out2_r, padd;
   wire 	clk_en;

   t_dspcore t_dspcore (/*AUTOINST*/
			// Outputs
			.out1_r		(out1_r),
			.pla_ph1	(pla_ph1),
			.pla_ph2	(pla_ph2),
			// Inputs
			.dsp_ph1	(dsp_ph1),
			.dsp_ph2	(dsp_ph2),
			.dsp_reset	(dsp_reset),
			.clk_en		(clk_en));
   t_dsppla t_dsppla (/*AUTOINST*/
		      // Outputs
		      .out2_r		(out2_r[7:0]),
		      // Inputs
		      .pla_ph1		(pla_ph1),
		      .pla_ph2		(pla_ph2),
		      .dsp_reset	(dsp_reset),
		      .padd		(padd[7:0]));

   assign 	out = out1_r ? 8'h00 : out2_r;
   assign 	clk_en = 1'b1;

endmodule

module t_dspcore (/*AUTOARG*/
   // Outputs
   out1_r, pla_ph1, pla_ph2,
   // Inputs
   dsp_ph1, dsp_ph2, dsp_reset, clk_en
   );
   input dsp_ph1, dsp_ph2, dsp_reset;
   input clk_en;
   output out1_r, pla_ph1, pla_ph2;

   wire   dsp_ph1, dsp_ph2, dsp_reset;
   wire   pla_ph1, pla_ph2;
   reg 	  out1_r;

   always @(posedge dsp_ph1 or posedge dsp_reset) begin
      if (dsp_reset)
	out1_r <= 1'h0;
      else
	out1_r <= ~out1_r;
   end

   assign pla_ph1 = dsp_ph1;
   assign pla_ph2 = dsp_ph2 & clk_en;

endmodule

module t_dsppla (/*AUTOARG*/
   // Outputs
   out2_r,
   // Inputs
   pla_ph1, pla_ph2, dsp_reset, padd
   );
   input pla_ph1, pla_ph2, dsp_reset;
   input [7:0] padd;
   output [7:0] out2_r;

   wire 	pla_ph1, pla_ph2, dsp_reset;
   wire [7:0] 	padd;
   reg [7:0] 	out2_r;

   reg [7:0] 	latched_r;

   always @(posedge pla_ph1 or posedge dsp_reset) begin
      if (dsp_reset)
	latched_r <= 8'h00;
      else
	latched_r <= padd;
   end

   always @(posedge pla_ph2 or posedge dsp_reset) begin
      if (dsp_reset)
	out2_r <= 8'h00;
      else
	out2_r <= latched_r;
   end

endmodule
