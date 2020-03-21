// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   reg   b;

   wire  vconst1 = 1'b0;
   wire  vconst2 = !(vconst1);
   wire  vconst3 = !vconst2;
   wire  vconst = vconst3;

   wire       qa;
   wire       qb;
   wire       qc;
   wire       qd;
   wire       qe;
   ta ta (.b(b), .vconst(vconst), .q(qa));
   tb tb (.clk(clk), .vconst(vconst), .q(qb));
   tc tc (.b(b), .vconst(vconst), .q(qc));
   td td (.b(b), .vconst(vconst), .q(qd));
   te te (.clk(clk), .b(b), .vconst(vconst), .q(qe));

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $display("%b",{qa,qb,qc,qd,qe});
`endif
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    b <= 1'b1;
	 end
	 if (cyc==2) begin
	    if (qa!=1'b1) $stop;
	    if (qb!=1'b0) $stop;
	    if (qd!=1'b0) $stop;
	    b <= 1'b0;
	 end
	 if (cyc==3) begin
	    if (qa!=1'b0) $stop;
	    if (qb!=1'b0) $stop;
	    if (qd!=1'b0) $stop;
	    if (qe!=1'b0) $stop;
	    b <= 1'b1;
	 end
	 if (cyc==4) begin
	    if (qa!=1'b1) $stop;
	    if (qb!=1'b0) $stop;
	    if (qd!=1'b0) $stop;
	    if (qe!=1'b1) $stop;
	    b <= 1'b0;
	 end
	 if (cyc==5) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule

module ta (
	   input vconst,
	   input b,
	   output reg q);

   always @ (/*AS*/b or vconst) begin
      q = vconst | b;
   end
endmodule

module tb (
	   input vconst,
	   input clk,
	   output reg q);

   always @ (posedge clk) begin
      q <= vconst;
   end
endmodule

module tc (
	   input vconst,
	   input b,
	   output reg q);
   always @ (posedge vconst) begin
      q <= b;
      $stop;
   end
endmodule

module td (
	   input vconst,
	   input b,
	   output reg q);

   always @ (/*AS*/vconst) begin
     q = vconst;
   end
endmodule

module te (
	   input clk,
	   input vconst,
	   input b,
	   output reg q);
   reg 		  qmid;
   always @ (posedge vconst or posedge clk) begin
      qmid <= b;
   end
   always @ (posedge clk or posedge vconst) begin
      q <= qmid;
   end
endmodule
