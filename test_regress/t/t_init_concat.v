// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   reg [31:0]  wr_data;
   reg 	       wr_en;
   wire [31:0] rd_data;
   wire [1:0]  rd_guards;
   wire [1:0]  rd_guardsok;

   regfile regfile (/*AUTOINST*/
		    // Outputs
		    .rd_data		(rd_data[31:0]),
		    .rd_guards		(rd_guards[1:0]),
		    .rd_guardsok	(rd_guardsok[1:0]),
		    // Inputs
		    .wr_data		(wr_data[31:0]),
		    .wr_en		(wr_en),
		    .clk		(clk));

   initial wr_en = 0;

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    if (!rd_guards[0]) $stop;
	    if (!rd_guardsok[0]) $stop;
	    wr_en <= 1'b1;
	    wr_data <= 32'hfeedf;
	 end
	 if (cyc==2) begin
	    wr_en <= 0;
	 end
	 if (cyc==3) begin
	    wr_en <= 0;
	    if (rd_data != 32'hfeedf) $stop;
	    if (rd_guards != 2'b11) $stop;
	    if (rd_guardsok != 2'b11) $stop;
	 end
	 if (cyc==4) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule

module regfile (
		input [31:0]            wr_data,
		input                   wr_en,
		output reg [31:0] 	rd_data,
		output [1:0]            rd_guards /*verilator public*/,
		output [1:0]            rd_guardsok /*verilator public*/,
		input                   clk
		);

   always @(posedge clk) begin
      if (wr_en)
	begin
           rd_data <= wr_data;
	end
   end

   // this initial statement will induce correct initialize behavior
   // initial rd_guards= { 2'b11 };

   assign rd_guards= {
		      rd_data[0],
		      1'b1
		      };

   assign rd_guardsok[0] = 1'b1;
   assign rd_guardsok[1] = rd_data[0];

endmodule // regfile
