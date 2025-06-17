// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define check(got ,exp) do if ((got) !== (exp)) begin $write("%%Error: %s:%0d: cyc=%0d got='h%x exp='h%x\n", `__FILE__,`__LINE__, cyc, (got), (exp)); `stop; end while(0)

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [31:0] cyc = 0;
   reg [6:0] cntA = 0;
   reg [6:0] cntB = 0;
   reg [6:0] cntC = 0;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc[0])  cntA <= cntA + 7'd1;
      if (cntA[0]) cntB <= cntB + 7'd1;
      if (cntB[0]) cntC <= cntC + 7'd1;

      if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   // Should create decoder
   wire [127:0] cntAOneHot = {
     cntA == 7'd127,
     cntA == 7'd126,
     cntA == 7'd125,
     cntA == 7'd124,
     cntA == 7'd123,
     cntA == 7'd122,
     cntA == 7'd121,
     cntA == 7'd120,
     cntA == 7'd119,
     cntA == 7'd118,
     cntA == 7'd117,
     cntA == 7'd116,
     cntA == 7'd115,
     cntA == 7'd114,
     cntA == 7'd113,
     cntA == 7'd112,
     cntA == 7'd111,
     cntA == 7'd110,
     cntA == 7'd109,
     cntA == 7'd108,
     cntA == 7'd107,
     cntA == 7'd106,
     cntA == 7'd105,
     cntA == 7'd104,
     cntA == 7'd103,
     cntA == 7'd102,
     cntA == 7'd101,
     cntA == 7'd100,
     cntA == 7'd99,
     cntA == 7'd98,
     cntA == 7'd97,
     cntA == 7'd96,
     cntA == 7'd95,
     cntA == 7'd94,
     cntA == 7'd93,
     cntA == 7'd92,
     cntA == 7'd91,
     cntA == 7'd90,
     cntA == 7'd89,
     cntA == 7'd88,
     cntA == 7'd87,
     cntA == 7'd86,
     cntA == 7'd85,
     cntA == 7'd84,
     cntA == 7'd83,
     cntA == 7'd82,
     cntA == 7'd81,
     cntA == 7'd80,
     cntA == 7'd79,
     cntA == 7'd78,
     cntA == 7'd77,
     cntA == 7'd76,
     cntA == 7'd75,
     cntA == 7'd74,
     cntA == 7'd73,
     cntA == 7'd72,
     cntA == 7'd71,
     cntA == 7'd70,
     cntA == 7'd69,
     cntA == 7'd68,
     cntA == 7'd67,
     cntA == 7'd66,
     cntA == 7'd65,
     cntA == 7'd64,
     cntA == 7'd63,
     cntA == 7'd62,
     cntA == 7'd61,
     cntA == 7'd60,
     cntA == 7'd59,
     cntA == 7'd58,
     cntA == 7'd57,
     cntA == 7'd56,
     cntA == 7'd55,
     cntA == 7'd54,
     cntA == 7'd53,
     cntA == 7'd52,
     cntA == 7'd51,
     cntA == 7'd50,
     cntA == 7'd49,
     cntA == 7'd48,
     cntA == 7'd47,
     cntA == 7'd46,
     cntA == 7'd45,
     cntA == 7'd44,
     cntA == 7'd43,
     cntA == 7'd42,
     cntA == 7'd41,
     cntA == 7'd40,
     cntA == 7'd39,
     cntA == 7'd38,
     cntA == 7'd37,
     cntA == 7'd36,
     cntA == 7'd35,
     cntA == 7'd34,
     cntA == 7'd33,
     cntA == 7'd32,
     cntA == 7'd31,
     cntA == 7'd30,
     cntA == 7'd29,
     cntA == 7'd28,
     cntA == 7'd27,
     cntA == 7'd26,
     cntA == 7'd25,
     cntA == 7'd24,
     cntA == 7'd23,
     cntA == 7'd22,
     cntA == 7'd21,
     cntA == 7'd20,
     cntA == 7'd19,
     cntA == 7'd18,
     cntA == 7'd17,
     cntA == 7'd16,
     cntA == 7'd15,
     cntA == 7'd14,
     cntA == 7'd13,
     cntA == 7'd12,
     cntA == 7'd11,
     cntA == 7'd10,
     cntA == 7'd9,
     cntA == 7'd8,
     cntA == 7'd7,
     cntA == 7'd6,
     cntA == 7'd5,
     cntA == 7'd4,
     cntA == 7'd3,
     cntA == 7'd2,
     cntA == 7'd1,
     cntA == 7'd0
   };

   // Should create decoder - with temporary needed for index variabls
   wire [127:0] notCntAOneHot = {
     ~cntA == 7'd127,
     ~cntA == 7'd126,
     ~cntA == 7'd125,
     ~cntA == 7'd124,
     ~cntA == 7'd123,
     ~cntA == 7'd122,
     ~cntA == 7'd121,
     ~cntA == 7'd120,
     ~cntA == 7'd119,
     ~cntA == 7'd118,
     ~cntA == 7'd117,
     ~cntA == 7'd116,
     ~cntA == 7'd115,
     ~cntA == 7'd114,
     ~cntA == 7'd113,
     ~cntA == 7'd112,
     ~cntA == 7'd111,
     ~cntA == 7'd110,
     ~cntA == 7'd109,
     ~cntA == 7'd108,
     ~cntA == 7'd107,
     ~cntA == 7'd106,
     ~cntA == 7'd105,
     ~cntA == 7'd104,
     ~cntA == 7'd103,
     ~cntA == 7'd102,
     ~cntA == 7'd101,
     ~cntA == 7'd100,
     ~cntA == 7'd99,
     ~cntA == 7'd98,
     ~cntA == 7'd97,
     ~cntA == 7'd96,
     ~cntA == 7'd95,
     ~cntA == 7'd94,
     ~cntA == 7'd93,
     ~cntA == 7'd92,
     ~cntA == 7'd91,
     ~cntA == 7'd90,
     ~cntA == 7'd89,
     ~cntA == 7'd88,
     ~cntA == 7'd87,
     ~cntA == 7'd86,
     ~cntA == 7'd85,
     ~cntA == 7'd84,
     ~cntA == 7'd83,
     ~cntA == 7'd82,
     ~cntA == 7'd81,
     ~cntA == 7'd80,
     ~cntA == 7'd79,
     ~cntA == 7'd78,
     ~cntA == 7'd77,
     ~cntA == 7'd76,
     ~cntA == 7'd75,
     ~cntA == 7'd74,
     ~cntA == 7'd73,
     ~cntA == 7'd72,
     ~cntA == 7'd71,
     ~cntA == 7'd70,
     ~cntA == 7'd69,
     ~cntA == 7'd68,
     ~cntA == 7'd67,
     ~cntA == 7'd66,
     ~cntA == 7'd65,
     ~cntA == 7'd64,
     ~cntA == 7'd63,
     ~cntA == 7'd62,
     ~cntA == 7'd61,
     ~cntA == 7'd60,
     ~cntA == 7'd59,
     ~cntA == 7'd58,
     ~cntA == 7'd57,
     ~cntA == 7'd56,
     ~cntA == 7'd55,
     ~cntA == 7'd54,
     ~cntA == 7'd53,
     ~cntA == 7'd52,
     ~cntA == 7'd51,
     ~cntA == 7'd50,
     ~cntA == 7'd49,
     ~cntA == 7'd48,
     ~cntA == 7'd47,
     ~cntA == 7'd46,
     ~cntA == 7'd45,
     ~cntA == 7'd44,
     ~cntA == 7'd43,
     ~cntA == 7'd42,
     ~cntA == 7'd41,
     ~cntA == 7'd40,
     ~cntA == 7'd39,
     ~cntA == 7'd38,
     ~cntA == 7'd37,
     ~cntA == 7'd36,
     ~cntA == 7'd35,
     ~cntA == 7'd34,
     ~cntA == 7'd33,
     ~cntA == 7'd32,
     ~cntA == 7'd31,
     ~cntA == 7'd30,
     ~cntA == 7'd29,
     ~cntA == 7'd28,
     ~cntA == 7'd27,
     ~cntA == 7'd26,
     ~cntA == 7'd25,
     ~cntA == 7'd24,
     ~cntA == 7'd23,
     ~cntA == 7'd22,
     ~cntA == 7'd21,
     ~cntA == 7'd20,
     ~cntA == 7'd19,
     ~cntA == 7'd18,
     ~cntA == 7'd17,
     ~cntA == 7'd16,
     ~cntA == 7'd15,
     ~cntA == 7'd14,
     ~cntA == 7'd13,
     ~cntA == 7'd12,
     ~cntA == 7'd11,
     ~cntA == 7'd10,
     ~cntA == 7'd9,
     ~cntA == 7'd8,
     ~cntA == 7'd7,
     ~cntA == 7'd6,
     ~cntA == 7'd5,
     ~cntA == 7'd4,
     ~cntA == 7'd3,
     ~cntA == 7'd2,
     ~cntA == 7'd1,
     ~cntA == 7'd0
   };

   // Should create decoder
   wire stupidWayToWriteConstOne = 1'b0
     + (cntB == 7'd127)
     + (cntB == 7'd126)
     + (cntB == 7'd125)
     + (cntB == 7'd124)
     + (cntB == 7'd123)
     + (cntB == 7'd122)
     + (cntB == 7'd121)
     + (cntB == 7'd120)
     + (cntB == 7'd119)
     + (cntB == 7'd118)
     + (cntB == 7'd117)
     + (cntB == 7'd116)
     + (cntB == 7'd115)
     + (cntB == 7'd114)
     + (cntB == 7'd113)
     + (cntB == 7'd112)
     + (cntB == 7'd111)
     + (cntB == 7'd110)
     + (cntB == 7'd109)
     + (cntB == 7'd108)
     + (cntB == 7'd107)
     + (cntB == 7'd106)
     + (cntB == 7'd105)
     + (cntB == 7'd104)
     + (cntB == 7'd103)
     + (cntB == 7'd102)
     + (cntB == 7'd101)
     + (cntB == 7'd100)
     + (cntB == 7'd99)
     + (cntB == 7'd98)
     + (cntB == 7'd97)
     + (cntB == 7'd96)
     + (cntB == 7'd95)
     + (cntB == 7'd94)
     + (cntB == 7'd93)
     + (cntB == 7'd92)
     + (cntB == 7'd91)
     + (cntB == 7'd90)
     + (cntB == 7'd89)
     + (cntB == 7'd88)
     + (cntB == 7'd87)
     + (cntB == 7'd86)
     + (cntB == 7'd85)
     + (cntB == 7'd84)
     + (cntB == 7'd83)
     + (cntB == 7'd82)
     + (cntB == 7'd81)
     + (cntB == 7'd80)
     + (cntB == 7'd79)
     + (cntB == 7'd78)
     + (cntB == 7'd77)
     + (cntB == 7'd76)
     + (cntB == 7'd75)
     + (cntB == 7'd74)
     + (cntB == 7'd73)
     + (cntB == 7'd72)
     + (cntB == 7'd71)
     + (cntB == 7'd70)
     + (cntB == 7'd69)
     + (cntB == 7'd68)
     + (cntB == 7'd67)
     + (cntB == 7'd66)
     + (cntB == 7'd65)
     + (cntB == 7'd64)
     + (cntB == 7'd63)
     + (cntB == 7'd62)
     + (cntB == 7'd61)
     + (cntB == 7'd60)
     + (cntB == 7'd59)
     + (cntB == 7'd58)
     + (cntB == 7'd57)
     + (cntB == 7'd56)
     + (cntB == 7'd55)
     + (cntB == 7'd54)
     + (cntB == 7'd53)
     + (cntB == 7'd52)
     + (cntB == 7'd51)
     + (cntB == 7'd50)
     + (cntB == 7'd49)
     + (cntB == 7'd48)
     + (cntB == 7'd47)
     + (cntB == 7'd46)
     + (cntB == 7'd45)
     + (cntB == 7'd44)
     + (cntB == 7'd43)
     + (cntB == 7'd42)
     + (cntB == 7'd41)
     + (cntB == 7'd40)
     + (cntB == 7'd39)
     + (cntB == 7'd38)
     + (cntB == 7'd37)
     + (cntB == 7'd36)
     + (cntB == 7'd35)
     + (cntB == 7'd34)
     + (cntB == 7'd33)
     + (cntB == 7'd32)
     + (cntB == 7'd31)
     + (cntB == 7'd30)
     + (cntB == 7'd29)
     + (cntB == 7'd28)
     + (cntB == 7'd27)
     + (cntB == 7'd26)
     + (cntB == 7'd25)
     + (cntB == 7'd24)
     + (cntB == 7'd23)
     + (cntB == 7'd22)
     + (cntB == 7'd21)
     + (cntB == 7'd20)
     + (cntB == 7'd19)
     + (cntB == 7'd18)
     + (cntB <= 7'd17);

   // Should not create decoder
   wire [6:0] twiceCntC =
     cntC == 7'd127 ? (7'd127 * 7'd2) :
     cntC == 7'd126 ? (7'd126 * 7'd2) :
     cntC == 7'd125 ? (7'd125 * 7'd2) :
     cntC == 7'd124 ? (7'd124 * 7'd2) :
     cntC == 7'd123 ? (7'd123 * 7'd2) :
     cntC == 7'd122 ? (7'd122 * 7'd2) :
     cntC == 7'd121 ? (7'd121 * 7'd2) :
     cntC == 7'd120 ? (7'd120 * 7'd2) :
     cntC == 7'd119 ? (7'd119 * 7'd2) :
     cntC == 7'd118 ? (7'd118 * 7'd2) :
     cntC == 7'd117 ? (7'd117 * 7'd2) :
     cntC == 7'd116 ? (7'd116 * 7'd2) :
     cntC == 7'd115 ? (7'd115 * 7'd2) :
     cntC == 7'd114 ? (7'd114 * 7'd2) :
     cntC == 7'd113 ? (7'd113 * 7'd2) :
     cntC == 7'd112 ? (7'd112 * 7'd2) :
     cntC == 7'd111 ? (7'd111 * 7'd2) :
     cntC == 7'd110 ? (7'd110 * 7'd2) :
     cntC == 7'd109 ? (7'd109 * 7'd2) :
     cntC == 7'd108 ? (7'd108 * 7'd2) :
     cntC == 7'd107 ? (7'd107 * 7'd2) :
     cntC == 7'd106 ? (7'd106 * 7'd2) :
     cntC == 7'd105 ? (7'd105 * 7'd2) :
     cntC == 7'd104 ? (7'd104 * 7'd2) :
     cntC == 7'd103 ? (7'd103 * 7'd2) :
     cntC == 7'd102 ? (7'd102 * 7'd2) :
     cntC == 7'd101 ? (7'd101 * 7'd2) :
     cntC == 7'd100 ? (7'd100 * 7'd2) :
     cntC == 7'd99 ? (7'd99 * 7'd2) :
     cntC == 7'd98 ? (7'd98 * 7'd2) :
     cntC == 7'd97 ? (7'd97 * 7'd2) :
     cntC == 7'd96 ? (7'd96 * 7'd2) :
     cntC == 7'd95 ? (7'd95 * 7'd2) :
     cntC == 7'd94 ? (7'd94 * 7'd2) :
     cntC == 7'd93 ? (7'd93 * 7'd2) :
     cntC == 7'd92 ? (7'd92 * 7'd2) :
     cntC == 7'd91 ? (7'd91 * 7'd2) :
     cntC == 7'd90 ? (7'd90 * 7'd2) :
     cntC == 7'd89 ? (7'd89 * 7'd2) :
     cntC == 7'd88 ? (7'd88 * 7'd2) :
     cntC == 7'd87 ? (7'd87 * 7'd2) :
     cntC == 7'd86 ? (7'd86 * 7'd2) :
     cntC == 7'd85 ? (7'd85 * 7'd2) :
     cntC == 7'd84 ? (7'd84 * 7'd2) :
     cntC == 7'd83 ? (7'd83 * 7'd2) :
     cntC == 7'd82 ? (7'd82 * 7'd2) :
     cntC == 7'd81 ? (7'd81 * 7'd2) :
     cntC == 7'd80 ? (7'd80 * 7'd2) :
     cntC == 7'd79 ? (7'd79 * 7'd2) :
     cntC == 7'd78 ? (7'd78 * 7'd2) :
     cntC == 7'd77 ? (7'd77 * 7'd2) :
     cntC == 7'd76 ? (7'd76 * 7'd2) :
     cntC == 7'd75 ? (7'd75 * 7'd2) :
     cntC == 7'd74 ? (7'd74 * 7'd2) :
     cntC == 7'd73 ? (7'd73 * 7'd2) :
     cntC == 7'd72 ? (7'd72 * 7'd2) :
     cntC == 7'd71 ? (7'd71 * 7'd2) :
     cntC == 7'd70 ? (7'd70 * 7'd2) :
     cntC == 7'd69 ? (7'd69 * 7'd2) :
     cntC == 7'd68 ? (7'd68 * 7'd2) :
     cntC == 7'd67 ? (7'd67 * 7'd2) :
     cntC == 7'd66 ? (7'd66 * 7'd2) :
     cntC == 7'd65 ? (7'd65 * 7'd2) :
     cntC == 7'd64 ? (7'd64 * 7'd2) :
     cntC == 7'd63 ? (7'd63 * 7'd2) :
     cntC == 7'd62 ? (7'd62 * 7'd2) :
     cntC == 7'd61 ? (7'd61 * 7'd2) :
     cntC == 7'd60 ? (7'd60 * 7'd2) :
     cntC == 7'd59 ? (7'd59 * 7'd2) :
     cntC == 7'd58 ? (7'd58 * 7'd2) :
     cntC == 7'd57 ? (7'd57 * 7'd2) :
     cntC == 7'd56 ? (7'd56 * 7'd2) :
     cntC == 7'd55 ? (7'd55 * 7'd2) :
     cntC == 7'd54 ? (7'd54 * 7'd2) :
     cntC == 7'd53 ? (7'd53 * 7'd2) :
     cntC == 7'd52 ? (7'd52 * 7'd2) :
     cntC == 7'd51 ? (7'd51 * 7'd2) :
     cntC == 7'd50 ? (7'd50 * 7'd2) :
     cntC == 7'd49 ? (7'd49 * 7'd2) :
     cntC == 7'd48 ? (7'd48 * 7'd2) :
     cntC == 7'd47 ? (7'd47 * 7'd2) :
     cntC == 7'd46 ? (7'd46 * 7'd2) :
     cntC == 7'd45 ? (7'd45 * 7'd2) :
     cntC == 7'd44 ? (7'd44 * 7'd2) :
     cntC == 7'd43 ? (7'd43 * 7'd2) :
     cntC == 7'd42 ? (7'd42 * 7'd2) :
     cntC == 7'd41 ? (7'd41 * 7'd2) :
     cntC == 7'd40 ? (7'd40 * 7'd2) :
     cntC == 7'd39 ? (7'd39 * 7'd2) :
     cntC == 7'd38 ? (7'd38 * 7'd2) :
     cntC == 7'd37 ? (7'd37 * 7'd2) :
     cntC == 7'd36 ? (7'd36 * 7'd2) :
     cntC == 7'd35 ? (7'd35 * 7'd2) :
     cntC == 7'd34 ? (7'd34 * 7'd2) :
     cntC == 7'd33 ? (7'd33 * 7'd2) :
     cntC == 7'd32 ? (7'd32 * 7'd2) :
     cntC == 7'd31 ? (7'd31 * 7'd2) :
     cntC == 7'd30 ? (7'd30 * 7'd2) :
     cntC == 7'd29 ? (7'd29 * 7'd2) :
     cntC == 7'd28 ? (7'd28 * 7'd2) :
     cntC == 7'd27 ? (7'd27 * 7'd2) :
     cntC == 7'd26 ? (7'd26 * 7'd2) :
     cntC == 7'd25 ? (7'd25 * 7'd2) :
     cntC == 7'd24 ? (7'd24 * 7'd2) :
     cntC == 7'd23 ? (7'd23 * 7'd2) :
     cntC == 7'd22 ? (7'd22 * 7'd2) :
     cntC == 7'd21 ? (7'd21 * 7'd2) :
     cntC == 7'd20 ? (7'd20 * 7'd2) :
     cntC == 7'd19 ? (7'd19 * 7'd2) :
     cntC == 7'd18 ? (7'd18 * 7'd2) :
     cntC == 7'd17 ? (7'd17 * 7'd2) :
     cntC == 7'd16 ? (7'd16 * 7'd2) :
     cntC == 7'd15 ? (7'd15 * 7'd2) :
     cntC == 7'd14 ? (7'd14 * 7'd2) :
     cntC == 7'd13 ? (7'd13 * 7'd2) :
     cntC == 7'd12 ? (7'd12 * 7'd2) :
     cntC == 7'd11 ? (7'd11 * 7'd2) :
     cntC == 7'd10 ? (7'd10 * 7'd2) :
     cntC == 7'd9 ? (7'd9 * 7'd2) :
     cntC == 7'd8 ? (7'd8 * 7'd2) :
     cntC == 7'd7 ? (7'd7 * 7'd2) :
     cntC == 7'd6 ? (7'd6 * 7'd2) :
     cntC == 7'd5 ? (7'd5 * 7'd2) :
     cntC == 7'd4 ? (7'd4 * 7'd2) :
     cntC == 7'd3 ? (7'd3 * 7'd2) :
     cntC == 7'd2 ? (7'd2 * 7'd2) :
     cntC == 7'd1 ? (7'd1 * 7'd2) : 7'd0;

   always @(posedge clk) begin
      `check(cntAOneHot[cntA], 1'b1);
      for (int i = 0; i < $bits(cntAOneHot); i = i + 1) begin
          if (i == int'(cntA)) continue;
         `check(cntAOneHot[i], 1'b0);
      end

      `check(notCntAOneHot[~cntA], 1'b1);
      for (int i = 0; i < $bits(notCntAOneHot); i = i + 1) begin
          if (i == {25'd0, ~cntA}) continue;
         `check(notCntAOneHot[i], 1'b0);
      end

      `check(stupidWayToWriteConstOne, 1'b1);

      `check(twiceCntC, cntC * 7'd2);
   end

endmodule
