// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   data_out,
   // Inputs
   wr, wa, rst_l, rd, ra, data_in, clk
   );
   input clk;

   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input [31:0]		data_in;		// To sub of reg_1r1w.v
   input [7:0]		ra;			// To sub of reg_1r1w.v
   input		rd;			// To sub of reg_1r1w.v
   input		rst_l;			// To sub of reg_1r1w.v
   input [7:0]		wa;			// To sub of reg_1r1w.v
   input		wr;			// To sub of reg_1r1w.v
   // End of automatics
   /*AUTOOUTPUT*/
   // Beginning of automatic outputs (from unused autoinst outputs)
   output [31:0]	data_out;		// From sub of reg_1r1w.v
   // End of automatics

   reg_1r1w #(.WIDTH(32), .DEPTH(256), .ADRWID(8))
   sub
     (/*AUTOINST*/
      // Outputs
      .data_out				(data_out[31:0]),
      // Inputs
      .data_in				(data_in[31:0]),
      .ra				(ra[7:0]),
      .wa				(wa[7:0]),
      .wr				(wr),
      .rd				(rd),
      .clk				(clk),
      .rst_l				(rst_l));

endmodule

module reg_1r1w
   #(
     parameter WIDTH=32,
     parameter ADRWID=10,
     parameter DEPTH=1024,
     parameter RST=0
     )
    (/*AUTOARG*/
   // Outputs
   data_out,
   // Inputs
   data_in, ra, wa, wr, rd, clk, rst_l
   );

    input [WIDTH-1:0] data_in;
    input [ADRWID-1:0] ra;
    input [ADRWID-1:0] wa;
    input wr;
    input rd;
    input clk;
    input rst_l;

    output [WIDTH-1:0] data_out;

    reg [WIDTH-1:0] array [DEPTH-1:0];
    reg [ADRWID-1:0] ra_r, wa_r;
    reg [WIDTH-1:0]  data_in_r;
    reg             wr_r;
    reg             rd_r;

    integer        x;

    // Message 679
    always @(posedge clk) begin
       int tmp = x + 1;
       if (tmp !== x + 1) $stop;
    end

    always @(posedge clk or negedge rst_l) begin
       if (!rst_l) begin
	  for (x=0; x<DEPTH; x=x+1) begin // <== VERILATOR FLAGS THIS LINE
             if (RST == 1) begin
		array[x] <= 0;
             end
	  end
	  ra_r <= 0;
	  wa_r <= 0;
	  wr_r <= 0;
	  rd_r <= 0;
	  data_in_r <= 0;
       end
       else begin
	  ra_r <= ra;
	  wa_r <= wa;
	  wr_r <= wr;
	  rd_r <= rd;
	  data_in_r <= data_in;
	  if (wr_r) array[wa_r] <= data_in_r;
       end
    end
endmodule

// Local Variables:
// verilog-auto-inst-param-value: t
// End:
