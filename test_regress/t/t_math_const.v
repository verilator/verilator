// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [39:0] con1,con2, con3;
   reg [31:0] w32;
   reg [31:0] v32 [2];

   // surefire lint_off UDDSCN
   reg [200:0] conw3, conw4;
   // surefire lint_on  UDDSCN

   reg [16*8-1:0] con__ascii;

   reg [31:0] win;
   // Test casting is proper on narrow->wide->narrow conversions
   // verilator lint_off WIDTH
   wire [49:0] 	  wider = ({18'h0, win} | (1'b1<<32)) - 50'h111;
   wire [31:0] 	  wider2 = ({win} | (1'b1<<32)) - 50'd111;
   // verilator lint_on WIDTH
   wire [31:0] 	  narrow = wider[31:0];
   wire [31:0] 	  narrow2 = wider2[31:0];

   // surefire lint_off ASWEMB
   // surefire lint_off ASWCMB
   // surefire lint_off CWECBB
   // surefire lint_off CWECSB

   // surefire lint_off STMINI
   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    $write("[%0t] t_const: Running\n",$time);

	    con1 = 4_0'h1000_0010;	// Odd but legal _ in width
	    con2 = 40'h10_0000_0010;
	    con3 = con1 + 40'h10_1100_0101;
	    if (con1[31:0]!== 32'h1000_0010 || con1[39:32]!==0) $stop;
	    $display("%x  %x %x\n", con2, con2[31:0], con2[39:32]);
	    if (con2[31:0]!== 32'h10 || con2[39:32]!==8'h10) $stop;
	    if (con3[31:0]!==32'h2100_0111 || con3[39:32]!==8'h10) $stop;

	    // verilator lint_off WIDTH
	    con1 = 10'h10 + 40'h80_1100_0131;
	    // verilator lint_on WIDTH
	    con2 = 40'h80_0000_0000 + 40'h13_7543_0107;
	    if (con1[31:0]!== 32'h1100_0141 || con1[39:32]!==8'h80) $stop;
	    if (con2[31:0]!== 32'h7543_0107 || con2[39:32]!==8'h93) $stop;

	    // verilator lint_off WIDTH
            conw3 = 94'h000a_5010_4020_3030_2040_1050;
	    // verilator lint_on WIDTH
	    if (conw3[31:00]!== 32'h2040_1050 ||
		conw3[63:32]!== 32'h4020_3030 ||
		conw3[95:64]!== 32'h000a_5010 ||
		conw3[128:96]!==33'h0) $stop;
	    $display("%x... %x\n", conw3[15:0], ~| conw3[15:0]);
	    if ((~| conw3[15:0]) !== 1'h0) $stop;
	    if ((~& conw3[15:0]) !== 1'h1) $stop;

	    // verilator lint_off WIDTH
            conw4 = 112'h7010_602a_5030_4040_3050_2060_1070;
	    // verilator lint_on WIDTH
	    if (conw4[31:00]!== 32'h2060_1070 ||
		conw4[63:32]!== 32'h4040_3050 ||
		conw4[95:64]!== 32'h602a_5030 ||
		conw4[127:96]!==32'h7010) $stop;
            // conw4 = 144'h7000_7000_7010_602a_5030_4040_3050_2060_1070;

	    w32 = 12;
	    win <= 12;
	    if ((32'hffff0000 >> w32) != 32'h 000ffff0) $stop;

	    con__ascii = "abcdefghijklmnop";
	    if ( con__ascii !== {"abcd","efgh","ijkl","mnop"}) $stop;
	    con__ascii = "abcdefghijklm";
	    if ( con__ascii !== {24'h0,"a","bcde","fghi","jklm"}) $stop;

	    if ( 3'dx !== 3'hx) $stop;

	    // Wide decimal
	    if ( 94'd12345678901234567890123456789 != 94'h27e41b3246bec9b16e398115) $stop;
	    if (-94'sd123456789012345678901234567 != 94'h3f99e1020ea70d57d360b479) $stop;

	    // Increments
	    w32 = 12; w32++;  if (w32 != 13) $stop;
	    w32 = 12; ++w32;  if (w32 != 13) $stop;
	    w32 = 12; w32--;  if (w32 != 11) $stop;
	    w32 = 12; --w32;  if (w32 != 11) $stop;
	    w32 = 12; w32 += 2; if (w32 != 14) $stop;
	    w32 = 12; w32 -= 2; if (w32 != 10) $stop;
	    w32 = 12; w32 *= 2; if (w32 != 24) $stop;
	    w32 = 12; w32 /= 2; if (w32 != 6) $stop;
	    w32 = 12; w32 &= 6; if (w32 != 4) $stop;
	    w32 = 12; w32 |= 15; if (w32 != 15) $stop;
	    w32 = 12; w32 ^= 15; if (w32 != 3) $stop;
	    w32 = 12; w32 >>= 1; if (w32 != 6) $stop;
	    w32 = 12; w32 <<= 1; if (w32 != 24) $stop;

	    // Increments
	    v32[1] = 12; v32[1]++;  if (v32[1] != 13) $stop;
	    v32[1] = 12; ++v32[1];  if (v32[1] != 13) $stop;
	    v32[1] = 12; v32[1]--;  if (v32[1] != 11) $stop;
	    v32[1] = 12; --v32[1];  if (v32[1] != 11) $stop;
	    v32[1] = 12; v32[1] += 2; if (v32[1] != 14) $stop;
	    v32[1] = 12; v32[1] -= 2; if (v32[1] != 10) $stop;
	    v32[1] = 12; v32[1] *= 2; if (v32[1] != 24) $stop;
	    v32[1] = 12; v32[1] /= 2; if (v32[1] != 6) $stop;
	    v32[1] = 12; v32[1] &= 6; if (v32[1] != 4) $stop;
	    v32[1] = 12; v32[1] |= 15; if (v32[1] != 15) $stop;
	    v32[1] = 12; v32[1] ^= 15; if (v32[1] != 3) $stop;
	    v32[1] = 12; v32[1] >>= 1; if (v32[1] != 6) $stop;
	    v32[1] = 12; v32[1] <<= 1; if (v32[1] != 24) $stop;
	 end
	 if (cyc==2) begin
	    win <= 32'h123123;
	    if (narrow !== 32'hfffffefb) $stop;
	    if (narrow2 !== 32'hffffff9d) $stop;
	 end
	 if (cyc==3) begin
	    if (narrow !== 32'h00123012) $stop;
	    if (narrow2 !== 32'h001230b4) $stop;
	 end
	 if (cyc==10) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule
