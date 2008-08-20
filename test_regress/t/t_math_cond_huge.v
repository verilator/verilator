// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Take CRC data and apply to testblock inputs
   wire [7:0] 	sel = crc[7:0];
   wire [255+3:0]  in = {crc[2:0],crc,crc,crc,crc};

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [3:0]		out;			// From test of Test.v
   // End of automatics

   /* Test AUTO_TEMPLATE (
    .i\([0-9]+\)	(in[\1 +:4]),
    ); */

   Test test (/*AUTOINST*/
	      // Outputs
	      .out			(out[3:0]),
	      // Inputs
	      .sel			(sel[7:0]),
	      .i0			(in[0 +:4]),		 // Templated
	      .i1			(in[1 +:4]),		 // Templated
	      .i2			(in[2 +:4]),		 // Templated
	      .i3			(in[3 +:4]),		 // Templated
	      .i4			(in[4 +:4]),		 // Templated
	      .i5			(in[5 +:4]),		 // Templated
	      .i6			(in[6 +:4]),		 // Templated
	      .i7			(in[7 +:4]),		 // Templated
	      .i8			(in[8 +:4]),		 // Templated
	      .i9			(in[9 +:4]),		 // Templated
	      .i10			(in[10 +:4]),		 // Templated
	      .i11			(in[11 +:4]),		 // Templated
	      .i12			(in[12 +:4]),		 // Templated
	      .i13			(in[13 +:4]),		 // Templated
	      .i14			(in[14 +:4]),		 // Templated
	      .i15			(in[15 +:4]),		 // Templated
	      .i16			(in[16 +:4]),		 // Templated
	      .i17			(in[17 +:4]),		 // Templated
	      .i18			(in[18 +:4]),		 // Templated
	      .i19			(in[19 +:4]),		 // Templated
	      .i20			(in[20 +:4]),		 // Templated
	      .i21			(in[21 +:4]),		 // Templated
	      .i22			(in[22 +:4]),		 // Templated
	      .i23			(in[23 +:4]),		 // Templated
	      .i24			(in[24 +:4]),		 // Templated
	      .i25			(in[25 +:4]),		 // Templated
	      .i26			(in[26 +:4]),		 // Templated
	      .i27			(in[27 +:4]),		 // Templated
	      .i28			(in[28 +:4]),		 // Templated
	      .i29			(in[29 +:4]),		 // Templated
	      .i30			(in[30 +:4]),		 // Templated
	      .i31			(in[31 +:4]),		 // Templated
	      .i32			(in[32 +:4]),		 // Templated
	      .i33			(in[33 +:4]),		 // Templated
	      .i34			(in[34 +:4]),		 // Templated
	      .i35			(in[35 +:4]),		 // Templated
	      .i36			(in[36 +:4]),		 // Templated
	      .i37			(in[37 +:4]),		 // Templated
	      .i38			(in[38 +:4]),		 // Templated
	      .i39			(in[39 +:4]),		 // Templated
	      .i40			(in[40 +:4]),		 // Templated
	      .i41			(in[41 +:4]),		 // Templated
	      .i42			(in[42 +:4]),		 // Templated
	      .i43			(in[43 +:4]),		 // Templated
	      .i44			(in[44 +:4]),		 // Templated
	      .i45			(in[45 +:4]),		 // Templated
	      .i46			(in[46 +:4]),		 // Templated
	      .i47			(in[47 +:4]),		 // Templated
	      .i48			(in[48 +:4]),		 // Templated
	      .i49			(in[49 +:4]),		 // Templated
	      .i50			(in[50 +:4]),		 // Templated
	      .i51			(in[51 +:4]),		 // Templated
	      .i52			(in[52 +:4]),		 // Templated
	      .i53			(in[53 +:4]),		 // Templated
	      .i54			(in[54 +:4]),		 // Templated
	      .i55			(in[55 +:4]),		 // Templated
	      .i56			(in[56 +:4]),		 // Templated
	      .i57			(in[57 +:4]),		 // Templated
	      .i58			(in[58 +:4]),		 // Templated
	      .i59			(in[59 +:4]),		 // Templated
	      .i60			(in[60 +:4]),		 // Templated
	      .i61			(in[61 +:4]),		 // Templated
	      .i62			(in[62 +:4]),		 // Templated
	      .i63			(in[63 +:4]),		 // Templated
	      .i64			(in[64 +:4]),		 // Templated
	      .i65			(in[65 +:4]),		 // Templated
	      .i66			(in[66 +:4]),		 // Templated
	      .i67			(in[67 +:4]),		 // Templated
	      .i68			(in[68 +:4]),		 // Templated
	      .i69			(in[69 +:4]),		 // Templated
	      .i70			(in[70 +:4]),		 // Templated
	      .i71			(in[71 +:4]),		 // Templated
	      .i72			(in[72 +:4]),		 // Templated
	      .i73			(in[73 +:4]),		 // Templated
	      .i74			(in[74 +:4]),		 // Templated
	      .i75			(in[75 +:4]),		 // Templated
	      .i76			(in[76 +:4]),		 // Templated
	      .i77			(in[77 +:4]),		 // Templated
	      .i78			(in[78 +:4]),		 // Templated
	      .i79			(in[79 +:4]),		 // Templated
	      .i80			(in[80 +:4]),		 // Templated
	      .i81			(in[81 +:4]),		 // Templated
	      .i82			(in[82 +:4]),		 // Templated
	      .i83			(in[83 +:4]),		 // Templated
	      .i84			(in[84 +:4]),		 // Templated
	      .i85			(in[85 +:4]),		 // Templated
	      .i86			(in[86 +:4]),		 // Templated
	      .i87			(in[87 +:4]),		 // Templated
	      .i88			(in[88 +:4]),		 // Templated
	      .i89			(in[89 +:4]),		 // Templated
	      .i90			(in[90 +:4]),		 // Templated
	      .i91			(in[91 +:4]),		 // Templated
	      .i92			(in[92 +:4]),		 // Templated
	      .i93			(in[93 +:4]),		 // Templated
	      .i94			(in[94 +:4]),		 // Templated
	      .i95			(in[95 +:4]),		 // Templated
	      .i96			(in[96 +:4]),		 // Templated
	      .i97			(in[97 +:4]),		 // Templated
	      .i98			(in[98 +:4]),		 // Templated
	      .i99			(in[99 +:4]),		 // Templated
	      .i100			(in[100 +:4]),		 // Templated
	      .i101			(in[101 +:4]),		 // Templated
	      .i102			(in[102 +:4]),		 // Templated
	      .i103			(in[103 +:4]),		 // Templated
	      .i104			(in[104 +:4]),		 // Templated
	      .i105			(in[105 +:4]),		 // Templated
	      .i106			(in[106 +:4]),		 // Templated
	      .i107			(in[107 +:4]),		 // Templated
	      .i108			(in[108 +:4]),		 // Templated
	      .i109			(in[109 +:4]),		 // Templated
	      .i110			(in[110 +:4]),		 // Templated
	      .i111			(in[111 +:4]),		 // Templated
	      .i112			(in[112 +:4]),		 // Templated
	      .i113			(in[113 +:4]),		 // Templated
	      .i114			(in[114 +:4]),		 // Templated
	      .i115			(in[115 +:4]),		 // Templated
	      .i116			(in[116 +:4]),		 // Templated
	      .i117			(in[117 +:4]),		 // Templated
	      .i118			(in[118 +:4]),		 // Templated
	      .i119			(in[119 +:4]),		 // Templated
	      .i120			(in[120 +:4]),		 // Templated
	      .i121			(in[121 +:4]),		 // Templated
	      .i122			(in[122 +:4]),		 // Templated
	      .i123			(in[123 +:4]),		 // Templated
	      .i124			(in[124 +:4]),		 // Templated
	      .i125			(in[125 +:4]),		 // Templated
	      .i126			(in[126 +:4]),		 // Templated
	      .i127			(in[127 +:4]),		 // Templated
	      .i128			(in[128 +:4]),		 // Templated
	      .i129			(in[129 +:4]),		 // Templated
	      .i130			(in[130 +:4]),		 // Templated
	      .i131			(in[131 +:4]),		 // Templated
	      .i132			(in[132 +:4]),		 // Templated
	      .i133			(in[133 +:4]),		 // Templated
	      .i134			(in[134 +:4]),		 // Templated
	      .i135			(in[135 +:4]),		 // Templated
	      .i136			(in[136 +:4]),		 // Templated
	      .i137			(in[137 +:4]),		 // Templated
	      .i138			(in[138 +:4]),		 // Templated
	      .i139			(in[139 +:4]),		 // Templated
	      .i140			(in[140 +:4]),		 // Templated
	      .i141			(in[141 +:4]),		 // Templated
	      .i142			(in[142 +:4]),		 // Templated
	      .i143			(in[143 +:4]),		 // Templated
	      .i144			(in[144 +:4]),		 // Templated
	      .i145			(in[145 +:4]),		 // Templated
	      .i146			(in[146 +:4]),		 // Templated
	      .i147			(in[147 +:4]),		 // Templated
	      .i148			(in[148 +:4]),		 // Templated
	      .i149			(in[149 +:4]),		 // Templated
	      .i150			(in[150 +:4]),		 // Templated
	      .i151			(in[151 +:4]),		 // Templated
	      .i152			(in[152 +:4]),		 // Templated
	      .i153			(in[153 +:4]),		 // Templated
	      .i154			(in[154 +:4]),		 // Templated
	      .i155			(in[155 +:4]),		 // Templated
	      .i156			(in[156 +:4]),		 // Templated
	      .i157			(in[157 +:4]),		 // Templated
	      .i158			(in[158 +:4]),		 // Templated
	      .i159			(in[159 +:4]),		 // Templated
	      .i160			(in[160 +:4]),		 // Templated
	      .i161			(in[161 +:4]),		 // Templated
	      .i162			(in[162 +:4]),		 // Templated
	      .i163			(in[163 +:4]),		 // Templated
	      .i164			(in[164 +:4]),		 // Templated
	      .i165			(in[165 +:4]),		 // Templated
	      .i166			(in[166 +:4]),		 // Templated
	      .i167			(in[167 +:4]),		 // Templated
	      .i168			(in[168 +:4]),		 // Templated
	      .i169			(in[169 +:4]),		 // Templated
	      .i170			(in[170 +:4]),		 // Templated
	      .i171			(in[171 +:4]),		 // Templated
	      .i172			(in[172 +:4]),		 // Templated
	      .i173			(in[173 +:4]),		 // Templated
	      .i174			(in[174 +:4]),		 // Templated
	      .i175			(in[175 +:4]),		 // Templated
	      .i176			(in[176 +:4]),		 // Templated
	      .i177			(in[177 +:4]),		 // Templated
	      .i178			(in[178 +:4]),		 // Templated
	      .i179			(in[179 +:4]),		 // Templated
	      .i180			(in[180 +:4]),		 // Templated
	      .i181			(in[181 +:4]),		 // Templated
	      .i182			(in[182 +:4]),		 // Templated
	      .i183			(in[183 +:4]),		 // Templated
	      .i184			(in[184 +:4]),		 // Templated
	      .i185			(in[185 +:4]),		 // Templated
	      .i186			(in[186 +:4]),		 // Templated
	      .i187			(in[187 +:4]),		 // Templated
	      .i188			(in[188 +:4]),		 // Templated
	      .i189			(in[189 +:4]),		 // Templated
	      .i190			(in[190 +:4]),		 // Templated
	      .i191			(in[191 +:4]),		 // Templated
	      .i192			(in[192 +:4]),		 // Templated
	      .i193			(in[193 +:4]),		 // Templated
	      .i194			(in[194 +:4]),		 // Templated
	      .i195			(in[195 +:4]),		 // Templated
	      .i196			(in[196 +:4]),		 // Templated
	      .i197			(in[197 +:4]),		 // Templated
	      .i198			(in[198 +:4]),		 // Templated
	      .i199			(in[199 +:4]),		 // Templated
	      .i200			(in[200 +:4]),		 // Templated
	      .i201			(in[201 +:4]),		 // Templated
	      .i202			(in[202 +:4]),		 // Templated
	      .i203			(in[203 +:4]),		 // Templated
	      .i204			(in[204 +:4]),		 // Templated
	      .i205			(in[205 +:4]),		 // Templated
	      .i206			(in[206 +:4]),		 // Templated
	      .i207			(in[207 +:4]),		 // Templated
	      .i208			(in[208 +:4]),		 // Templated
	      .i209			(in[209 +:4]),		 // Templated
	      .i210			(in[210 +:4]),		 // Templated
	      .i211			(in[211 +:4]),		 // Templated
	      .i212			(in[212 +:4]),		 // Templated
	      .i213			(in[213 +:4]),		 // Templated
	      .i214			(in[214 +:4]),		 // Templated
	      .i215			(in[215 +:4]),		 // Templated
	      .i216			(in[216 +:4]),		 // Templated
	      .i217			(in[217 +:4]),		 // Templated
	      .i218			(in[218 +:4]),		 // Templated
	      .i219			(in[219 +:4]),		 // Templated
	      .i220			(in[220 +:4]),		 // Templated
	      .i221			(in[221 +:4]),		 // Templated
	      .i222			(in[222 +:4]),		 // Templated
	      .i223			(in[223 +:4]),		 // Templated
	      .i224			(in[224 +:4]),		 // Templated
	      .i225			(in[225 +:4]),		 // Templated
	      .i226			(in[226 +:4]),		 // Templated
	      .i227			(in[227 +:4]),		 // Templated
	      .i228			(in[228 +:4]),		 // Templated
	      .i229			(in[229 +:4]),		 // Templated
	      .i230			(in[230 +:4]),		 // Templated
	      .i231			(in[231 +:4]),		 // Templated
	      .i232			(in[232 +:4]),		 // Templated
	      .i233			(in[233 +:4]),		 // Templated
	      .i234			(in[234 +:4]),		 // Templated
	      .i235			(in[235 +:4]),		 // Templated
	      .i236			(in[236 +:4]),		 // Templated
	      .i237			(in[237 +:4]),		 // Templated
	      .i238			(in[238 +:4]),		 // Templated
	      .i239			(in[239 +:4]),		 // Templated
	      .i240			(in[240 +:4]),		 // Templated
	      .i241			(in[241 +:4]),		 // Templated
	      .i242			(in[242 +:4]),		 // Templated
	      .i243			(in[243 +:4]),		 // Templated
	      .i244			(in[244 +:4]),		 // Templated
	      .i245			(in[245 +:4]),		 // Templated
	      .i246			(in[246 +:4]),		 // Templated
	      .i247			(in[247 +:4]),		 // Templated
	      .i248			(in[248 +:4]),		 // Templated
	      .i249			(in[249 +:4]),		 // Templated
	      .i250			(in[250 +:4]),		 // Templated
	      .i251			(in[251 +:4]),		 // Templated
	      .i252			(in[252 +:4]),		 // Templated
	      .i253			(in[253 +:4]),		 // Templated
	      .i254			(in[254 +:4]),		 // Templated
	      .i255			(in[255 +:4]));		 // Templated

   // Aggregate outputs into a single result vector
   wire [63:0] result = {60'h0, out};

   // What checksum will we end up with
`define EXPECTED_SUM 64'h36f3051d15caf07a

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test
  ( output wire [3:0] out,

    input [7:0] sel,

    input [3:0] i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16,
    i17, i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29, i30, i31, i32, i33,
    i34, i35, i36, i37, i38, i39, i40, i41, i42, i43, i44, i45, i46, i47, i48, i49, i50,
    i51, i52, i53, i54, i55, i56, i57, i58, i59, i60, i61, i62, i63, i64, i65, i66, i67,
    i68, i69, i70, i71, i72, i73, i74, i75, i76, i77, i78, i79, i80, i81, i82, i83, i84,
    i85, i86, i87, i88, i89, i90, i91, i92, i93, i94, i95, i96, i97, i98, i99, i100, i101,
    i102, i103, i104, i105, i106, i107, i108, i109, i110, i111, i112, i113, i114, i115,
    i116, i117, i118, i119, i120, i121, i122, i123, i124, i125, i126, i127, i128, i129,
    i130, i131, i132, i133, i134, i135, i136, i137, i138, i139, i140, i141, i142, i143,
    i144, i145, i146, i147, i148, i149, i150, i151, i152, i153, i154, i155, i156, i157,
    i158, i159, i160, i161, i162, i163, i164, i165, i166, i167, i168, i169, i170, i171,
    i172, i173, i174, i175, i176, i177, i178, i179, i180, i181, i182, i183, i184, i185,
    i186, i187, i188, i189, i190, i191, i192, i193, i194, i195, i196, i197, i198, i199,
    i200, i201, i202, i203, i204, i205, i206, i207, i208, i209, i210, i211, i212, i213,
    i214, i215, i216, i217, i218, i219, i220, i221, i222, i223, i224, i225, i226, i227,
    i228, i229, i230, i231, i232, i233, i234, i235, i236, i237, i238, i239, i240, i241,
    i242, i243, i244, i245, i246, i247, i248, i249, i250, i251, i252, i253, i254, i255
   );

   assign out
     = (sel==8'h00) ? i0 : (sel==8'h01) ? i1 : (sel==8'h02) ? i2 : (sel==8'h03) ? i3
       : (sel==8'h04) ? i4 : (sel==8'h05) ? i5 : (sel==8'h06) ? i6 : (sel==8'h07) ? i7
       : (sel==8'h08) ? i8 : (sel==8'h09) ? i9 : (sel==8'h0a) ? i10 : (sel==8'h0b) ? i11
       : (sel==8'h0c) ? i12 : (sel==8'h0d) ? i13 : (sel==8'h0e) ? i14 : (sel==8'h0f) ? i15
       : (sel==8'h10) ? i16 : (sel==8'h11) ? i17 : (sel==8'h12) ? i18 : (sel==8'h13) ? i19
       : (sel==8'h14) ? i20 : (sel==8'h15) ? i21 : (sel==8'h16) ? i22 : (sel==8'h17) ? i23
       : (sel==8'h18) ? i24 : (sel==8'h19) ? i25 : (sel==8'h1a) ? i26 : (sel==8'h1b) ? i27
       : (sel==8'h1c) ? i28 : (sel==8'h1d) ? i29 : (sel==8'h1e) ? i30 : (sel==8'h1f) ? i31
       : (sel==8'h20) ? i32 : (sel==8'h21) ? i33 : (sel==8'h22) ? i34 : (sel==8'h23) ? i35
       : (sel==8'h24) ? i36 : (sel==8'h25) ? i37 : (sel==8'h26) ? i38 : (sel==8'h27) ? i39
       : (sel==8'h28) ? i40 : (sel==8'h29) ? i41 : (sel==8'h2a) ? i42 : (sel==8'h2b) ? i43
       : (sel==8'h2c) ? i44 : (sel==8'h2d) ? i45 : (sel==8'h2e) ? i46 : (sel==8'h2f) ? i47
       : (sel==8'h30) ? i48 : (sel==8'h31) ? i49 : (sel==8'h32) ? i50 : (sel==8'h33) ? i51
       : (sel==8'h34) ? i52 : (sel==8'h35) ? i53 : (sel==8'h36) ? i54 : (sel==8'h37) ? i55
       : (sel==8'h38) ? i56 : (sel==8'h39) ? i57 : (sel==8'h3a) ? i58 : (sel==8'h3b) ? i59
       : (sel==8'h3c) ? i60 : (sel==8'h3d) ? i61 : (sel==8'h3e) ? i62 : (sel==8'h3f) ? i63
       : (sel==8'h40) ? i64 : (sel==8'h41) ? i65 : (sel==8'h42) ? i66 : (sel==8'h43) ? i67
       : (sel==8'h44) ? i68 : (sel==8'h45) ? i69 : (sel==8'h46) ? i70 : (sel==8'h47) ? i71
       : (sel==8'h48) ? i72 : (sel==8'h49) ? i73 : (sel==8'h4a) ? i74 : (sel==8'h4b) ? i75
       : (sel==8'h4c) ? i76 : (sel==8'h4d) ? i77 : (sel==8'h4e) ? i78 : (sel==8'h4f) ? i79
       : (sel==8'h50) ? i80 : (sel==8'h51) ? i81 : (sel==8'h52) ? i82 : (sel==8'h53) ? i83
       : (sel==8'h54) ? i84 : (sel==8'h55) ? i85 : (sel==8'h56) ? i86 : (sel==8'h57) ? i87
       : (sel==8'h58) ? i88 : (sel==8'h59) ? i89 : (sel==8'h5a) ? i90 : (sel==8'h5b) ? i91
       : (sel==8'h5c) ? i92 : (sel==8'h5d) ? i93 : (sel==8'h5e) ? i94 : (sel==8'h5f) ? i95
       : (sel==8'h60) ? i96 : (sel==8'h61) ? i97 : (sel==8'h62) ? i98 : (sel==8'h63) ? i99
       : (sel==8'h64) ? i100 : (sel==8'h65) ? i101 : (sel==8'h66) ? i102 : (sel==8'h67) ? i103
       : (sel==8'h68) ? i104 : (sel==8'h69) ? i105 : (sel==8'h6a) ? i106 : (sel==8'h6b) ? i107
       : (sel==8'h6c) ? i108 : (sel==8'h6d) ? i109 : (sel==8'h6e) ? i110 : (sel==8'h6f) ? i111
       : (sel==8'h70) ? i112 : (sel==8'h71) ? i113 : (sel==8'h72) ? i114 : (sel==8'h73) ? i115
       : (sel==8'h74) ? i116 : (sel==8'h75) ? i117 : (sel==8'h76) ? i118 : (sel==8'h77) ? i119
       : (sel==8'h78) ? i120 : (sel==8'h79) ? i121 : (sel==8'h7a) ? i122 : (sel==8'h7b) ? i123
       : (sel==8'h7c) ? i124 : (sel==8'h7d) ? i125 : (sel==8'h7e) ? i126 : (sel==8'h7f) ? i127
       : (sel==8'h80) ? i128 : (sel==8'h81) ? i129 : (sel==8'h82) ? i130 : (sel==8'h83) ? i131
       : (sel==8'h84) ? i132 : (sel==8'h85) ? i133 : (sel==8'h86) ? i134 : (sel==8'h87) ? i135
       : (sel==8'h88) ? i136 : (sel==8'h89) ? i137 : (sel==8'h8a) ? i138 : (sel==8'h8b) ? i139
       : (sel==8'h8c) ? i140 : (sel==8'h8d) ? i141 : (sel==8'h8e) ? i142 : (sel==8'h8f) ? i143
       : (sel==8'h90) ? i144 : (sel==8'h91) ? i145 : (sel==8'h92) ? i146 : (sel==8'h93) ? i147
       : (sel==8'h94) ? i148 : (sel==8'h95) ? i149 : (sel==8'h96) ? i150 : (sel==8'h98) ? i151
       : (sel==8'h99) ? i152 : (sel==8'h9a) ? i153 : (sel==8'h9b) ? i154 : (sel==8'h9c) ? i155
       : (sel==8'h9d) ? i156 : (sel==8'h9e) ? i157 : (sel==8'h9f) ? i158 : (sel==8'ha0) ? i159
       : (sel==8'ha1) ? i160 : (sel==8'ha2) ? i161 : (sel==8'ha3) ? i162 : (sel==8'ha4) ? i163
       : (sel==8'ha5) ? i164 : (sel==8'ha6) ? i165 : (sel==8'ha7) ? i166 : (sel==8'ha8) ? i167
       : (sel==8'ha9) ? i168 : (sel==8'haa) ? i169 : (sel==8'hab) ? i170 : (sel==8'hac) ? i171
       : (sel==8'had) ? i172 : (sel==8'hae) ? i173 : (sel==8'haf) ? i174 : (sel==8'hb0) ? i175
       : (sel==8'hb1) ? i176 : (sel==8'hb2) ? i177 : (sel==8'hb3) ? i178 : (sel==8'hb4) ? i179
       : (sel==8'hb5) ? i180 : (sel==8'hb6) ? i181 : (sel==8'hb7) ? i182 : (sel==8'hb8) ? i183
       : (sel==8'hb9) ? i184 : (sel==8'hba) ? i185 : (sel==8'hbb) ? i186 : (sel==8'hbc) ? i187
       : (sel==8'hbd) ? i188 : (sel==8'hbe) ? i189 : (sel==8'hbf) ? i190 : (sel==8'hc0) ? i191
       : (sel==8'hc1) ? i192 : (sel==8'hc2) ? i193 : (sel==8'hc3) ? i194 : (sel==8'hc4) ? i195
       : (sel==8'hc5) ? i196 : (sel==8'hc6) ? i197 : (sel==8'hc7) ? i198 : (sel==8'hc8) ? i199
       : (sel==8'hc9) ? i200 : (sel==8'hca) ? i201 : (sel==8'hcb) ? i202 : (sel==8'hcc) ? i203
       : (sel==8'hcd) ? i204 : (sel==8'hce) ? i205 : (sel==8'hcf) ? i206 : (sel==8'hd0) ? i207
       : (sel==8'hd1) ? i208 : (sel==8'hd2) ? i209 : (sel==8'hd3) ? i210 : (sel==8'hd4) ? i211
       : (sel==8'hd5) ? i212 : (sel==8'hd6) ? i213 : (sel==8'hd7) ? i214 : (sel==8'hd8) ? i215
       : (sel==8'hd9) ? i216 : (sel==8'hda) ? i217 : (sel==8'hdb) ? i218 : (sel==8'hdc) ? i219
       : (sel==8'hdd) ? i220 : (sel==8'hde) ? i221 : (sel==8'hdf) ? i222 : (sel==8'he0) ? i223
       : (sel==8'he1) ? i224 : (sel==8'he2) ? i225 : (sel==8'he3) ? i226 : (sel==8'he4) ? i227
       : (sel==8'he5) ? i228 : (sel==8'he6) ? i229 : (sel==8'he7) ? i230 : (sel==8'he8) ? i231
       : (sel==8'he9) ? i232 : (sel==8'hea) ? i233 : (sel==8'heb) ? i234 : (sel==8'hec) ? i235
       : (sel==8'hed) ? i236 : (sel==8'hee) ? i237 : (sel==8'hef) ? i238 : (sel==8'hf0) ? i239
       : (sel==8'hf1) ? i240 : (sel==8'hf2) ? i241 : (sel==8'hf3) ? i242 : (sel==8'hf4) ? i243
       : (sel==8'hf5) ? i244 : (sel==8'hf6) ? i245 : (sel==8'hf7) ? i246 : (sel==8'hf8) ? i247
       : (sel==8'hf9) ? i248 : (sel==8'hfa) ? i249 : (sel==8'hfb) ? i250 : (sel==8'hfc) ? i251
       : (sel==8'hfd) ? i252 : (sel==8'hfe) ? i253 : (sel==8'hff) ? i254 : i255;

endmodule
