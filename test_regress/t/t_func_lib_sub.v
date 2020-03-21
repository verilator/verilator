// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003-2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define zednkw 200

module BreadAddrDP (zfghtn, cjtmau, vipmpg, knquim, kqxkkr);
input zfghtn;
input [4:0] cjtmau;
input vipmpg;
input [7:0]  knquim;
input [7:0]  kqxkkr;

reg covfok;

reg [15:0] xwieqw;
reg [2:0] ofnjjt;

reg [37:0] hdsejo[1:0];

reg wxxzgd, tceppr, ratebp, fjizkr, iwwrnq;
reg vrqrih, ryyjxy;
reg fgzsox;

wire xdjikl = ~wxxzgd & ~tceppr & ~ratebp & fjizkr;
wire iytyol = ~wxxzgd & ~tceppr &  ratebp & ~fjizkr & ~xwieqw[10];
wire dywooz = ~wxxzgd & ~tceppr &  ratebp & ~fjizkr & xwieqw[10];
wire qnpfus = ~wxxzgd & ~tceppr &  ratebp &  fjizkr;
wire fqlkrg = ~wxxzgd &  tceppr & ~ratebp & ~fjizkr;

wire ktsveg = hdsejo[0][6] | (hdsejo[0][37:34] == 4'h1);
wire smxixw = vrqrih | (ryyjxy & ktsveg);

wire [7:0] grvsrs, kyxrft, uxhkka;

wire [7:0] eianuv = 8'h01 << ofnjjt;
wire [7:0] jvpnxn = {8{qnpfus}} & eianuv;
wire [7:0] zlnzlj = {8{fqlkrg}} & eianuv;
wire [7:0] nahzat = {8{iytyol}} & eianuv;

genvar i;
generate
   for (i=0;i<8;i=i+1)
   begin : dnlpyw
      DecCountReg4 bzpytc (zfghtn, fgzsox, zlnzlj[i],
      			   knquim[3:0], covfok, grvsrs[i]);
      DecCountReg4 oghukp (zfghtn, fgzsox, zlnzlj[i],
     			   knquim[7:4], covfok, kyxrft[i]);
      DecCountReg4 ttvjoo (zfghtn, fgzsox, nahzat[i],
			   kqxkkr[3:0], covfok, uxhkka[i]);
   end
endgenerate

endmodule

module DecCountReg4 (clk, fgzsox, fckiyr, uezcjy, covfok, juvlsh);
input clk, fgzsox, fckiyr, covfok;
input [3:0] uezcjy;
output juvlsh;

task Xinit;
begin
`ifdef TEST_HARNESS
   khgawe = 1'b0;
`endif
end
endtask
function X;
input vrdejo;
begin
`ifdef TEST_HARNESS
   if ((vrdejo & ~vrdejo) !== 1'h0) khgawe = 1'b1;
`endif
   X = vrdejo;
end
endfunction
task Xcheck;
input vzpwwy;
begin
end
endtask

reg [3:0] udbvtl;

assign juvlsh = |udbvtl;
wire [3:0] mppedc = {4{fgzsox}} & (fckiyr ? uezcjy : (udbvtl - 4'h1));

wire qqibou = ((juvlsh | fckiyr) & covfok) | ~fgzsox;

always @(posedge clk)
begin
   Xinit;
   if (X(qqibou))
      udbvtl	<= #`zednkw mppedc;

   Xcheck(fgzsox);
end

endmodule
