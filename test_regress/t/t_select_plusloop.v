// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [31:0] narrow;
   reg [63:0] quad;
   reg [127:0] wide;

   integer cyc; initial cyc=0;
   reg [7:0] crc;
   reg [6:0] index;

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%0d crc=%b n=%x\n",$time, cyc, crc, narrow);
      cyc <= cyc + 1;
      if (cyc==0) begin
	 // Setup
	 narrow <= 32'h0;
	 quad <= 64'h0;
	 wide <= 128'h0;
	 crc <= 8'hed;
	 index <= 7'h0;
      end
      else if (cyc<90) begin
	 index <= index + 7'h2;
	 crc <= {crc[6:0], ~^ {crc[7],crc[5],crc[4],crc[3]}};
	 // verilator lint_off WIDTH
	 if (index < 9'd20)  narrow[index +: 3] <= crc[2:0];
	 if (index < 9'd60)  quad  [index +: 3] <= crc[2:0];
	 if (index < 9'd120) wide  [index +: 3] <= crc[2:0];
	 //
	 narrow[index[3:0]] <= ~narrow[index[3:0]];
	 quad  [~index[3:0]]<= ~quad  [~index[3:0]];
	 wide  [~index[3:0]] <= ~wide [~index[3:0]];
	 // verilator lint_on WIDTH
      end
      else if (cyc==90) begin
	 wide[12 +: 4] <=4'h6;	quad[12 +: 4] <=4'h6;	narrow[12 +: 4] <=4'h6;
	 wide[42 +: 4] <=4'h6;	quad[42 +: 4] <=4'h6;
	 wide[82 +: 4] <=4'h6;
      end
      else if (cyc==91) begin
	 wide[0] <=1'b1;	quad[0] <=1'b1;		narrow[0] <=1'b1;
	 wide[41] <=1'b1;	quad[41] <=1'b1;
	 wide[81] <=1'b1;
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%b n=%x q=%x w=%x\n",$time, cyc, crc, narrow, quad, wide);
	 if (crc != 8'b01111001) $stop;
	 if (narrow != 32'h001661c7) $stop;
	 if (quad !=   64'h16d49b6f64266039) $stop;
	 if (wide !=  128'h012fd26d265b266ff6d49b6f64266039) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
