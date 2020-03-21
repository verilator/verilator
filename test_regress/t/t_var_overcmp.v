// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   dout,
   // Inputs
   clk, rstn, dval0, dval1, dbgsel_w
   );

   input clk;
   input rstn;
   input [7:0] dval0;
   input [7:0] dval1;
   input [7:0] dbgsel_w;
   output [7:0] dout;

   wire [7:0] 	dout = dout0 | dout1;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [7:0]		dout0;			// From sub0 of sub0.v
   wire [7:0]		dout1;			// From sub1 of sub1.v
   // End of automatics

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

   reg [7:0] 	dbgsel_msk;
   always_comb begin
      reg [7:0] mask;
      mask = 8'hff;
      dbgsel_msk = (dbgsel_w & mask);
   end

   reg [7:0] 	dbgsel;
   always @(posedge clk) begin
      if ((rstn == 0)) begin
         dbgsel <= 0;
      end
      else begin
         dbgsel <= dbgsel_msk;
      end
   end

   sub0 sub0 (/*AUTOINST*/
	      // Outputs
	      .dout0			(dout0[7:0]),
	      // Inputs
	      .rstn			(rstn),
	      .clk			(clk),
	      .dval1			(dval1[7:0]),
	      .dbgsel			(dbgsel[7:0]));
   sub1 sub1 (/*AUTOINST*/
	      // Outputs
	      .dout1			(dout1[7:0]),
	      // Inputs
	      .rstn			(rstn),
	      .clk			(clk),
	      .dval1			(dval1[7:0]),
	      .dbgsel			(dbgsel[7:0]));

endmodule

module sub0
  (
   /*AUTOARG*/
   // Outputs
   dout0,
   // Inputs
   rstn, clk, dval1, dbgsel
   );

   input rstn;
   input clk;
   input [7:0] dval1;
   input [7:0] dbgsel;
   output reg [7:0] dout0;

   reg [7:0] 	    dbgsel_d1r;

   always_comb begin
      // verilator lint_off WIDTH
      if (((dbgsel_d1r >= 34) && (dbgsel_d1r < 65))) begin
	 // verilator lint_on WIDTH
	 dout0 = dval1;
      end
      else begin
	 dout0 = 0;
      end
   end

   always @(posedge clk) begin
      if ((rstn == 0)) begin
         dbgsel_d1r <= 0;
      end
      else begin
         dbgsel_d1r <= dbgsel;
      end
   end

endmodule

module sub1
  (
   /*AUTOARG*/
   // Outputs
   dout1,
   // Inputs
   rstn, clk, dval1, dbgsel
   );

   input rstn;
   input clk;
   input [7:0] dval1;
   input [7:0] 	dbgsel;
   output reg [7:0] dout1;

   reg [7:0] 	dbgsel_d1r;

   always_comb begin
      // verilator lint_off WIDTH
      if (((dbgsel_d1r >= 334) && (dbgsel_d1r < 365))) begin
	 // verilator lint_on WIDTH
	 dout1 = dval1;
      end
      else begin
	 dout1 = 0;
      end
   end

   always @(posedge clk) begin
      if ((rstn == 0)) begin
         dbgsel_d1r <= 0;
      end
      else begin
         dbgsel_d1r <= dbgsel;
      end
   end

endmodule
