// -*- Verilog -*-
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t_math_wallace_mul (  /*AUTOARG*/
  // Outputs
  product_d3,
  // Inputs
  clk, enable, negate, datA, datB
  );

  input clk;
  input enable;
  input negate;

  input [31:0] datA;
  input [31:0] datB;

  output reg [64:0] product_d3;

  wire [129:0] l1ppin00;
  wire [129:0] l1ppin01;
  wire [129:0] l1ppin02;
  wire [129:0] l1ppin03;
  wire [129:0] l1ppin04;
  wire [129:0] l1ppin05;
  wire [129:0] l1ppin06;
  wire [129:0] l1ppin07;
  wire [129:0] l1ppin08;
  wire [129:0] l1ppin09;
  wire [129:0] l1ppin10;
  wire [129:0] l1ppin11;
  wire [129:0] l1ppin12;
  wire [129:0] l1ppin13;
  wire [129:0] l1ppin14;
  wire [129:0] l1ppin15;
  wire [129:0] l1ppin16;
  wire [129:0] l1ppin17;
  wire [129:0] l1ppin18;
  wire [129:0] l1ppin19;
  wire [129:0] l1ppin20;
  wire [129:0] l1ppin21;
  wire [129:0] l1ppin22;
  wire [129:0] l1ppin23;
  wire [129:0] l1ppin24;
  wire [129:0] l1ppin25;
  wire [129:0] l1ppin26;
  wire [129:0] l1ppin27;
  wire [129:0] l1ppin28;
  wire [129:0] l1ppin29;
  wire [129:0] l1ppin30;
  wire [129:0] l1ppin31;
  wire [129:0] l1ppin32;
  wire [129:0] l1ppin33;

  wire [63:0] l1sumg0;
  wire [63:0] l1sumg1;
  wire [63:0] l1sumg2;
  wire [63:0] l1sumg3;
  wire [63:0] l1carryg0;
  wire [63:0] l1carryg1;
  wire [63:0] l1carryg2;
  wire [63:0] l1carryg3;

  wire [63:0] l2sumg0;
  wire [63:0] l2carryg0;

  wire [64:0] l1cin0g0;
  wire [64:0] l1cin0g1;
  wire [64:0] l1cin0g2;
  wire [64:0] l1cin0g3;

  wire [64:0] l1cin1g0;
  wire [64:0] l1cin1g1;
  wire [64:0] l1cin1g2;
  wire [64:0] l1cin1g3;

  wire [64:0] l1cin2g0;
  wire [64:0] l1cin2g1;
  wire [64:0] l1cin2g2;
  wire [64:0] l1cin2g3;

  wire [64:0] l1cin3g0;
  wire [64:0] l1cin3g1;
  wire [64:0] l1cin3g2;

  wire [64:0] l1cin4g0;
  wire [64:0] l1cin4g1;
  wire [64:0] l1cin4g2;

  wire [64:0] l1cin5g0;
  wire [64:0] l1cin5g1;
  wire [64:0] l1cin5g2;

  wire [64:0] l2cin0g0;
  wire [64:0] l2cin1g0;
  wire [64:0] l2cin2g0;
  wire [64:0] l2cin3g0;
  wire [64:0] l2cin4g0;
  wire [64:0] l2cin5g0;

  reg enable_d1;
  reg enable_d2;
  reg enable_d3;
  reg negate_d1;
  reg [31:0] datA_d1;
  reg [31:0] datB_d1;

  always @(posedge clk) begin
    // Initial input gater
    enable_d1 <= enable;
    if (enable) begin
      negate_d1 <= negate;
      datA_d1 <= datA;
      datB_d1 <= datB;
    end
  end

  function [4:0] booth;
    input negatef;
    input [2:0] in;

    case (({3{negatef}} ^ in))
      3'b000: booth = 5'b0_0001;  // 0
      3'b001: booth = 5'b0_0100;  // +1x
      3'b010: booth = 5'b0_0100;  // +1x
      3'b011: booth = 5'b1_0000;  // +2x
      3'b100: booth = 5'b0_1000;  // -2x
      3'b101: booth = 5'b0_0010;  // -1x
      3'b110: booth = 5'b0_0010;  // -1x
      default: booth = 5'b0_0001;  // 0
    endcase
  endfunction

  wire [66:0] lcl_mier = {2'b0, 32'h0, datB_d1, 1'b0};

  integer j;

  reg [4:0] ppsel[32:0];

  always @* begin
    for (j = 0; j < 65; j = j + 2) begin
      ppsel[j/2] = booth(negate_d1, {lcl_mier[j+2], lcl_mier[j+1], lcl_mier[j]});
    end
  end

  TmpPpg ppgen (
      // Inputs
      .datA_d1(datA_d1),
      // Outputs
      .pp00(l1ppin00[129:0]),
      .pp01(l1ppin01[129:0]),
      .pp02(l1ppin02[129:0]),
      .pp03(l1ppin03[129:0]),
      .pp04(l1ppin04[129:0]),
      .pp05(l1ppin05[129:0]),
      .pp06(l1ppin06[129:0]),
      .pp07(l1ppin07[129:0]),
      .pp08(l1ppin08[129:0]),
      .pp09(l1ppin09[129:0]),
      .pp10(l1ppin10[129:0]),
      .pp11(l1ppin11[129:0]),
      .pp12(l1ppin12[129:0]),
      .pp13(l1ppin13[129:0]),
      .pp14(l1ppin14[129:0]),
      .pp15(l1ppin15[129:0]),
      .pp16(l1ppin16[129:0]),
      .pp17(l1ppin17[129:0]),
      .pp18(l1ppin18[129:0]),
      .pp19(l1ppin19[129:0]),
      .pp20(l1ppin20[129:0]),
      .pp21(l1ppin21[129:0]),
      .pp22(l1ppin22[129:0]),
      .pp23(l1ppin23[129:0]),
      .pp24(l1ppin24[129:0]),
      .pp25(l1ppin25[129:0]),
      .pp26(l1ppin26[129:0]),
      .pp27(l1ppin27[129:0]),
      .pp28(l1ppin28[129:0]),
      .pp29(l1ppin29[129:0]),
      .pp30(l1ppin30[129:0]),
      .pp31(l1ppin31[129:0]),
      .pp32(l1ppin32[129:0]),
      .pp33(l1ppin33[129:0]),
      // Inputs
      .pp00sel(ppsel[00][4:0]),
      .pp01sel(ppsel[01][4:0]),
      .pp02sel(ppsel[02][4:0]),
      .pp03sel(ppsel[03][4:0]),
      .pp04sel(ppsel[04][4:0]),
      .pp05sel(ppsel[05][4:0]),
      .pp06sel(ppsel[06][4:0]),
      .pp07sel(ppsel[07][4:0]),
      .pp08sel(ppsel[08][4:0]),
      .pp09sel(ppsel[09][4:0]),
      .pp10sel(ppsel[10][4:0]),
      .pp11sel(ppsel[11][4:0]),
      .pp12sel(ppsel[12][4:0]),
      .pp13sel(ppsel[13][4:0]),
      .pp14sel(ppsel[14][4:0]),
      .pp15sel(ppsel[15][4:0]),
      .pp16sel(ppsel[16][4:0]),
      .pp17sel(ppsel[17][4:0]),
      .pp18sel(ppsel[18][4:0]),
      .pp19sel(ppsel[19][4:0]),
      .pp20sel(ppsel[20][4:0]),
      .pp21sel(ppsel[21][4:0]),
      .pp22sel(ppsel[22][4:0]),
      .pp23sel(ppsel[23][4:0]),
      .pp24sel(ppsel[24][4:0]),
      .pp25sel(ppsel[25][4:0]),
      .pp26sel(ppsel[26][4:0]),
      .pp27sel(ppsel[27][4:0]),
      .pp28sel(ppsel[28][4:0]),
      .pp29sel(ppsel[29][4:0]),
      .pp30sel(ppsel[30][4:0]),
      .pp31sel(ppsel[31][4:0]),
      .pp32sel(ppsel[32][4:0])
  );

  assign l1cin0g0[0] = 1'b0;
  assign l1cin0g1[0] = 1'b0;
  assign l1cin0g2[0] = 1'b0;
  assign l1cin0g3[0] = 1'b0;

  assign l1cin1g0[0] = 1'b0;
  assign l1cin1g1[0] = 1'b0;
  assign l1cin1g2[0] = 1'b0;
  assign l1cin1g3[0] = 1'b0;

  assign l1cin2g0[0] = 1'b0;
  assign l1cin2g1[0] = 1'b0;
  assign l1cin2g2[0] = 1'b0;
  assign l1cin2g3[0] = 1'b0;

  assign l1cin3g0[0] = 1'b0;
  assign l1cin3g1[0] = 1'b0;
  assign l1cin3g2[0] = 1'b0;

  assign l1cin4g0[0] = 1'b0;
  assign l1cin4g1[0] = 1'b0;
  assign l1cin4g2[0] = 1'b0;

  assign l1cin5g0[0] = 1'b0;
  assign l1cin5g1[0] = 1'b0;
  assign l1cin5g2[0] = 1'b0;

  assign l2cin0g0[0] = 1'b0;
  assign l2cin1g0[0] = 1'b0;
  assign l2cin2g0[0] = 1'b0;
  assign l2cin3g0[0] = 1'b0;
  assign l2cin4g0[0] = 1'b0;
  assign l2cin5g0[0] = 1'b0;

  genvar i;
  generate
    for (i = 0; i < 64; i = i + 1) begin
      TmpCsa9to2 l1csag0 (
          // Outputs
          .cout0(l1cin0g0[i+1]),
          .cout1(l1cin1g0[i+1]),
          .cout2(l1cin2g0[i+1]),
          .cout3(l1cin3g0[i+1]),
          .cout4(l1cin4g0[i+1]),
          .cout5(l1cin5g0[i+1]),
          .carry(l1carryg0[i]),
          .sum(l1sumg0[i]),
          // Inputs
          .in0(l1ppin00[i]),
          .in1(l1ppin01[i]),
          .in2(l1ppin02[i]),
          .in3(l1ppin03[i]),
          .in4(l1ppin04[i]),
          .in5(l1ppin05[i]),
          .in6(l1ppin06[i]),
          .in7(l1ppin07[i]),
          .in8(l1ppin08[i]),
          .cin0(l1cin0g0[i]),
          .cin1(l1cin1g0[i]),
          .cin2(l1cin2g0[i]),
          .cin3(l1cin3g0[i]),
          .cin4(l1cin4g0[i]),
          .cin5(l1cin5g0[i])
      );

      TmpCsa9to2 l1csag1 (
          // Outputs
          .cout0(l1cin0g1[i+1]),
          .cout1(l1cin1g1[i+1]),
          .cout2(l1cin2g1[i+1]),
          .cout3(l1cin3g1[i+1]),
          .cout4(l1cin4g1[i+1]),
          .cout5(l1cin5g1[i+1]),
          .carry(l1carryg1[i]),
          .sum(l1sumg1[i]),
          // Inputs
          .in0(l1ppin09[i]),
          .in1(l1ppin10[i]),
          .in2(l1ppin11[i]),
          .in3(l1ppin12[i]),
          .in4(l1ppin13[i]),
          .in5(l1ppin14[i]),
          .in6(l1ppin15[i]),
          .in7(l1ppin16[i]),
          .in8(l1ppin17[i]),
          .cin0(l1cin0g1[i]),
          .cin1(l1cin1g1[i]),
          .cin2(l1cin2g1[i]),
          .cin3(l1cin3g1[i]),
          .cin4(l1cin4g1[i]),
          .cin5(l1cin5g1[i])
      );

      TmpCsa9to2 l1csag2 (
          // Outputs
          .cout0(l1cin0g2[i+1]),
          .cout1(l1cin1g2[i+1]),
          .cout2(l1cin2g2[i+1]),
          .cout3(l1cin3g2[i+1]),
          .cout4(l1cin4g2[i+1]),
          .cout5(l1cin5g2[i+1]),
          .carry(l1carryg2[i]),
          .sum(l1sumg2[i]),
          // Inputs
          .in0(l1ppin18[i]),
          .in1(l1ppin19[i]),
          .in2(l1ppin20[i]),
          .in3(l1ppin21[i]),
          .in4(l1ppin22[i]),
          .in5(l1ppin23[i]),
          .in6(l1ppin24[i]),
          .in7(l1ppin25[i]),
          .in8(l1ppin26[i]),
          .cin0(l1cin0g2[i]),
          .cin1(l1cin1g2[i]),
          .cin2(l1cin2g2[i]),
          .cin3(l1cin3g2[i]),
          .cin4(l1cin4g2[i]),
          .cin5(l1cin5g2[i])
      );

      TmpCsa6to2 l1csag3 (
          // Outputs
          .cout0(l1cin0g3[i+1]),
          .cout1(l1cin1g3[i+1]),
          .cout2(l1cin2g3[i+1]),
          .carry(l1carryg3[i]),
          .sum(l1sumg3[i]),
          // Inputs
          .in0(l1ppin27[i]),
          .in1(l1ppin28[i]),
          .in2(l1ppin29[i]),
          .in3(l1ppin30[i]),
          .in4(l1ppin31[i]),
          .in5(l1ppin32[i]),
          .cin0(l1cin0g3[i]),
          .cin1(l1cin1g3[i]),
          .cin2(l1cin2g3[i])
      );
    end
  endgenerate

  wire [63:0] l2ppin00 = l1sumg0[63:0];
  wire [63:0] l2ppin01 = {l1carryg0[62:0], 1'b0};
  wire [63:0] l2ppin02 = l1sumg1[63:0];
  wire [63:0] l2ppin03 = {l1carryg1[62:0], 1'b0};
  wire [63:0] l2ppin04 = l1sumg2[63:0];
  wire [63:0] l2ppin05 = {l1carryg2[62:0], 1'b0};
  wire [63:0] l2ppin06 = l1sumg3[63:0];
  wire [63:0] l2ppin07 = {l1carryg3[62:0], 1'b0};
  wire [63:0] l2ppin08 = l1ppin33[63:0];

  generate
    for (i = 0; i < 64; i = i + 1) begin
      TmpCsa9to2 l2csag0 (
          // Outputs
          .cout0(l2cin0g0[i+1]),
          .cout1(l2cin1g0[i+1]),
          .cout2(l2cin2g0[i+1]),
          .cout3(l2cin3g0[i+1]),
          .cout4(l2cin4g0[i+1]),
          .cout5(l2cin5g0[i+1]),
          .carry(l2carryg0[i]),
          .sum(l2sumg0[i]),
          // Inputs
          .in0(l2ppin00[i]),
          .in1(l2ppin01[i]),
          .in2(l2ppin02[i]),
          .in3(l2ppin03[i]),
          .in4(l2ppin04[i]),
          .in5(l2ppin05[i]),
          .in6(l2ppin06[i]),
          .in7(l2ppin07[i]),
          .in8(l2ppin08[i]),
          .cin0(l2cin0g0[i]),
          .cin1(l2cin1g0[i]),
          .cin2(l2cin2g0[i]),
          .cin3(l2cin3g0[i]),
          .cin4(l2cin4g0[i]),
          .cin5(l2cin5g0[i])
      );
    end
  endgenerate

  reg [63:0] l3ppin00_d2;
  reg [63:0] l3ppin01_d2;

  always @(posedge clk) begin
    enable_d2 <= enable_d1;
    if (enable_d1) begin
      l3ppin00_d2 <= l2sumg0[63:0];
      l3ppin01_d2 <= {l2carryg0[62:0], 1'b0};
    end
  end

  wire [63:0] l3carryg0_d2;
  wire [63:0] l3sumg0_d2;

  generate
    for (i = 0; i < 64; i = i + 1) begin
      TmpCsa3 l3csag0 (  // Outputs
          .out({l3carryg0_d2[i], l3sumg0_d2[i]}),
          // Inputs
          .in0(l3ppin00_d2[i]),
          .in1(l3ppin01_d2[i]),
          .in2(1'b0)
      );
    end
  endgenerate

  wire [64:0] temp_lo_d2 = {l3sumg0_d2[63:0]} + {l3carryg0_d2[62:0], 1'b0};

  always @(posedge clk) begin
    if (enable_d2) begin
      product_d3 <= temp_lo_d2;
    end
  end

  // lint_checking URDWIR OFF
  wire        _unused_ok = |{1'b0,
                              l1carryg0,
                              l1carryg1,
                              l1carryg2,
                              l1carryg3,
                              l1cin0g0,
                              l1cin0g1,
                              l1cin0g2,
                              l1cin0g3,
                              l1cin1g0,
                              l1cin1g1,
                              l1cin1g2,
                              l1cin1g3,
                              l1cin2g0,
                              l1cin2g1,
                              l1cin2g2,
                              l1cin2g3,
                              l1cin3g0,
                              l1cin3g1,
                              l1cin3g2,
                              l1cin4g0,
                              l1cin4g1,
                              l1cin4g2,
                              l1cin5g0,
                              l1cin5g1,
                              l1cin5g2,
                              l1ppin00,
                              l1ppin01,
                              l1ppin02,
                              l1ppin03,
                              l1ppin04,
                              l1ppin05,
                              l1ppin06,
                              l1ppin07,
                              l1ppin08,
                              l1ppin09,
                              l1ppin10,
                              l1ppin11,
                              l1ppin12,
                              l1ppin13,
                              l1ppin14,
                              l1ppin15,
                              l1ppin16,
                              l1ppin17,
                              l1ppin18,
                              l1ppin19,
                              l1ppin20,
                              l1ppin21,
                              l1ppin22,
                              l1ppin23,
                              l1ppin24,
                              l1ppin25,
                              l1ppin26,
                              l1ppin27,
                              l1ppin28,
                              l1ppin29,
                              l1ppin30,
                              l1ppin31,
                              l1ppin32,
                              l1ppin33,
                              l1sumg0,
                              l1sumg1,
                              l1sumg2,
                              l1sumg3,
                              l2carryg0,
                              l2cin0g0,
                              l2cin1g0,
                              l2cin2g0,
                              l2cin3g0,
                              l2cin4g0,
                              l2cin5g0,
                              l2sumg0,
                              l3carryg0_d2[63],
                              1'b0};

  // lint_checking URDWIR ON
endmodule

// lint_checking MULTMF OFF

module TmpPpg (  /*AUTOARG*/
  // Outputs
  pp00, pp01, pp02, pp03, pp04, pp05, pp06, pp07, pp08, pp09, pp10, pp11, pp12,
  pp13, pp14, pp15, pp16, pp17, pp18, pp19, pp20, pp21, pp22, pp23, pp24, pp25,
  pp26, pp27, pp28, pp29, pp30, pp31, pp32, pp33,
  // Inputs
  datA_d1, pp00sel, pp01sel, pp02sel, pp03sel, pp04sel, pp05sel, pp06sel,
  pp07sel, pp08sel, pp09sel, pp10sel, pp11sel, pp12sel, pp13sel, pp14sel,
  pp15sel, pp16sel, pp17sel, pp18sel, pp19sel, pp20sel, pp21sel, pp22sel,
  pp23sel, pp24sel, pp25sel, pp26sel, pp27sel, pp28sel, pp29sel, pp30sel,
  pp31sel, pp32sel
  );

  input [31:0] datA_d1;

  input [4:0] pp00sel;
  input [4:0] pp01sel;
  input [4:0] pp02sel;
  input [4:0] pp03sel;
  input [4:0] pp04sel;
  input [4:0] pp05sel;
  input [4:0] pp06sel;
  input [4:0] pp07sel;
  input [4:0] pp08sel;
  input [4:0] pp09sel;
  input [4:0] pp10sel;
  input [4:0] pp11sel;
  input [4:0] pp12sel;
  input [4:0] pp13sel;
  input [4:0] pp14sel;
  input [4:0] pp15sel;
  input [4:0] pp16sel;
  input [4:0] pp17sel;
  input [4:0] pp18sel;
  input [4:0] pp19sel;
  input [4:0] pp20sel;
  input [4:0] pp21sel;
  input [4:0] pp22sel;
  input [4:0] pp23sel;
  input [4:0] pp24sel;
  input [4:0] pp25sel;
  input [4:0] pp26sel;
  input [4:0] pp27sel;
  input [4:0] pp28sel;
  input [4:0] pp29sel;
  input [4:0] pp30sel;
  input [4:0] pp31sel;
  input [4:0] pp32sel;

  output [129:0] pp00;
  output [129:0] pp01;
  output [129:0] pp02;
  output [129:0] pp03;
  output [129:0] pp04;
  output [129:0] pp05;
  output [129:0] pp06;
  output [129:0] pp07;
  output [129:0] pp08;
  output [129:0] pp09;
  output [129:0] pp10;
  output [129:0] pp11;
  output [129:0] pp12;
  output [129:0] pp13;
  output [129:0] pp14;
  output [129:0] pp15;
  output [129:0] pp16;
  output [129:0] pp17;
  output [129:0] pp18;
  output [129:0] pp19;
  output [129:0] pp20;
  output [129:0] pp21;
  output [129:0] pp22;
  output [129:0] pp23;
  output [129:0] pp24;
  output [129:0] pp25;
  output [129:0] pp26;
  output [129:0] pp27;
  output [129:0] pp28;
  output [129:0] pp29;
  output [129:0] pp30;
  output [129:0] pp31;
  output [129:0] pp32;
  output [129:0] pp33;

  function [65:0] boothmux;
    input [4:0] mxsel;
    input [65:0] mpcnd;
    case (mxsel)
      5'b0_0001: boothmux = 66'h0;
      5'b0_0010: boothmux = ~mpcnd;  // -1x
      5'b0_0100: boothmux = mpcnd;  // +1x
      5'b0_1000: boothmux = ~{mpcnd[64:0], 1'b0};  // -2x
      5'b1_0000: boothmux = {mpcnd[64:0], 1'b0};  // +2x
      default: boothmux = 66'h0;  // CANNOT_HIT
    endcase
  endfunction

  function rowcin;
    input [4:0] mxsel;
    case (mxsel)
      5'b0_0001: rowcin = 1'b0;
      5'b0_0010: rowcin = 1'b1;  // -1x
      5'b0_0100: rowcin = 1'b0;  // +1x
      5'b0_1000: rowcin = 1'b1;  // -2x
      5'b1_0000: rowcin = 1'b0;  // +2x
      default: rowcin = 1'b0;  // CANNOT_HIT
    endcase
  endfunction

  wire [65:0] lcl_mand = {2'b0, 32'h0, datA_d1};

  wire [2*32+1:2*00] temp_pp00;
  wire [2*33+1:2*01] temp_pp01;
  wire [2*34+1:2*02] temp_pp02;
  wire [2*35+1:2*03] temp_pp03;
  wire [2*36+1:2*04] temp_pp04;
  wire [2*37+1:2*05] temp_pp05;
  wire [2*38+1:2*06] temp_pp06;
  wire [2*39+1:2*07] temp_pp07;
  wire [2*40+1:2*08] temp_pp08;
  wire [2*41+1:2*09] temp_pp09;
  wire [2*42+1:2*10] temp_pp10;
  wire [2*43+1:2*11] temp_pp11;
  wire [2*44+1:2*12] temp_pp12;
  wire [2*45+1:2*13] temp_pp13;
  wire [2*46+1:2*14] temp_pp14;
  wire [2*47+1:2*15] temp_pp15;
  wire [2*48+1:2*16] temp_pp16;
  wire [2*49+1:2*17] temp_pp17;
  wire [2*50+1:2*18] temp_pp18;
  wire [2*51+1:2*19] temp_pp19;
  wire [2*52+1:2*20] temp_pp20;
  wire [2*53+1:2*21] temp_pp21;
  wire [2*54+1:2*22] temp_pp22;
  wire [2*55+1:2*23] temp_pp23;
  wire [2*56+1:2*24] temp_pp24;
  wire [2*57+1:2*25] temp_pp25;
  wire [2*58+1:2*26] temp_pp26;
  wire [2*59+1:2*27] temp_pp27;
  wire [2*60+1:2*28] temp_pp28;
  wire [2*61+1:2*29] temp_pp29;
  wire [2*62+1:2*30] temp_pp30;
  wire [2*63+1:2*31] temp_pp31;
  wire [2*64+1:2*32] temp_pp32;

  assign temp_pp00 = boothmux(pp00sel, lcl_mand);
  assign temp_pp01 = boothmux(pp01sel, lcl_mand);
  assign temp_pp02 = boothmux(pp02sel, lcl_mand);
  assign temp_pp03 = boothmux(pp03sel, lcl_mand);
  assign temp_pp04 = boothmux(pp04sel, lcl_mand);
  assign temp_pp05 = boothmux(pp05sel, lcl_mand);
  assign temp_pp06 = boothmux(pp06sel, lcl_mand);
  assign temp_pp07 = boothmux(pp07sel, lcl_mand);
  assign temp_pp08 = boothmux(pp08sel, lcl_mand);
  assign temp_pp09 = boothmux(pp09sel, lcl_mand);
  assign temp_pp10 = boothmux(pp10sel, lcl_mand);
  assign temp_pp11 = boothmux(pp11sel, lcl_mand);
  assign temp_pp12 = boothmux(pp12sel, lcl_mand);
  assign temp_pp13 = boothmux(pp13sel, lcl_mand);
  assign temp_pp14 = boothmux(pp14sel, lcl_mand);
  assign temp_pp15 = boothmux(pp15sel, lcl_mand);
  assign temp_pp16 = boothmux(pp16sel, lcl_mand);
  assign temp_pp17 = boothmux(pp17sel, lcl_mand);
  assign temp_pp18 = boothmux(pp18sel, lcl_mand);
  assign temp_pp19 = boothmux(pp19sel, lcl_mand);
  assign temp_pp20 = boothmux(pp20sel, lcl_mand);
  assign temp_pp21 = boothmux(pp21sel, lcl_mand);
  assign temp_pp22 = boothmux(pp22sel, lcl_mand);
  assign temp_pp23 = boothmux(pp23sel, lcl_mand);
  assign temp_pp24 = boothmux(pp24sel, lcl_mand);
  assign temp_pp25 = boothmux(pp25sel, lcl_mand);
  assign temp_pp26 = boothmux(pp26sel, lcl_mand);
  assign temp_pp27 = boothmux(pp27sel, lcl_mand);
  assign temp_pp28 = boothmux(pp28sel, lcl_mand);
  assign temp_pp29 = boothmux(pp29sel, lcl_mand);
  assign temp_pp30 = boothmux(pp30sel, lcl_mand);
  assign temp_pp31 = boothmux(pp31sel, lcl_mand);
  assign temp_pp32 = boothmux(pp32sel, lcl_mand);

  assign pp00[2*32+1+3:2*00] = {
    ~temp_pp00[2*32+1], temp_pp00[2*32+1], temp_pp00[2*32+1], temp_pp00[2*32+1:2*00]
  };
  assign pp01[2*33+1+2:2*01] = {1'b1, ~temp_pp01[2*33+1], temp_pp01[2*33+1:2*01]};
  assign pp02[2*34+1+2:2*02] = {1'b1, ~temp_pp02[2*34+1], temp_pp02[2*34+1:2*02]};
  assign pp03[2*35+1+2:2*03] = {1'b1, ~temp_pp03[2*35+1], temp_pp03[2*35+1:2*03]};
  assign pp04[2*36+1+2:2*04] = {1'b1, ~temp_pp04[2*36+1], temp_pp04[2*36+1:2*04]};
  assign pp05[2*37+1+2:2*05] = {1'b1, ~temp_pp05[2*37+1], temp_pp05[2*37+1:2*05]};
  assign pp06[2*38+1+2:2*06] = {1'b1, ~temp_pp06[2*38+1], temp_pp06[2*38+1:2*06]};
  assign pp07[2*39+1+2:2*07] = {1'b1, ~temp_pp07[2*39+1], temp_pp07[2*39+1:2*07]};
  assign pp08[2*40+1+2:2*08] = {1'b1, ~temp_pp08[2*40+1], temp_pp08[2*40+1:2*08]};
  assign pp09[2*41+1+2:2*09] = {1'b1, ~temp_pp09[2*41+1], temp_pp09[2*41+1:2*09]};
  assign pp10[2*42+1+2:2*10] = {1'b1, ~temp_pp10[2*42+1], temp_pp10[2*42+1:2*10]};
  assign pp11[2*43+1+2:2*11] = {1'b1, ~temp_pp11[2*43+1], temp_pp11[2*43+1:2*11]};
  assign pp12[2*44+1+2:2*12] = {1'b1, ~temp_pp12[2*44+1], temp_pp12[2*44+1:2*12]};
  assign pp13[2*45+1+2:2*13] = {1'b1, ~temp_pp13[2*45+1], temp_pp13[2*45+1:2*13]};
  assign pp14[2*46+1+2:2*14] = {1'b1, ~temp_pp14[2*46+1], temp_pp14[2*46+1:2*14]};
  assign pp15[2*47+1+2:2*15] = {1'b1, ~temp_pp15[2*47+1], temp_pp15[2*47+1:2*15]};
  assign pp16[2*48+1+2:2*16] = {1'b1, ~temp_pp16[2*48+1], temp_pp16[2*48+1:2*16]};
  assign pp17[2*49+1+2:2*17] = {1'b1, ~temp_pp17[2*49+1], temp_pp17[2*49+1:2*17]};
  assign pp18[2*50+1+2:2*18] = {1'b1, ~temp_pp18[2*50+1], temp_pp18[2*50+1:2*18]};
  assign pp19[2*51+1+2:2*19] = {1'b1, ~temp_pp19[2*51+1], temp_pp19[2*51+1:2*19]};
  assign pp20[2*52+1+2:2*20] = {1'b1, ~temp_pp20[2*52+1], temp_pp20[2*52+1:2*20]};
  assign pp21[2*53+1+2:2*21] = {1'b1, ~temp_pp21[2*53+1], temp_pp21[2*53+1:2*21]};
  assign pp22[2*54+1+2:2*22] = {1'b1, ~temp_pp22[2*54+1], temp_pp22[2*54+1:2*22]};
  assign pp23[2*55+1+2:2*23] = {1'b1, ~temp_pp23[2*55+1], temp_pp23[2*55+1:2*23]};
  assign pp24[2*56+1+2:2*24] = {1'b1, ~temp_pp24[2*56+1], temp_pp24[2*56+1:2*24]};
  assign pp25[2*57+1+2:2*25] = {1'b1, ~temp_pp25[2*57+1], temp_pp25[2*57+1:2*25]};
  assign pp26[2*58+1+2:2*26] = {1'b1, ~temp_pp26[2*58+1], temp_pp26[2*58+1:2*26]};
  assign pp27[2*59+1+2:2*27] = {1'b1, ~temp_pp27[2*59+1], temp_pp27[2*59+1:2*27]};
  assign pp28[2*60+1+2:2*28] = {1'b1, ~temp_pp28[2*60+1], temp_pp28[2*60+1:2*28]};
  assign pp29[2*61+1+2:2*29] = {1'b1, ~temp_pp29[2*61+1], temp_pp29[2*61+1:2*29]};
  assign pp30[2*62+1+2:2*30] = {1'b1, ~temp_pp30[2*62+1], temp_pp30[2*62+1:2*30]};
  assign pp31[2*63+1+2:2*31] = {1'b1, ~temp_pp31[2*63+1], temp_pp31[2*63+1:2*31]};
  assign pp32[2*63+1+2:2*32] = temp_pp32[2*64+1:2*32];
  assign pp33[2*63+1+2:2*33] = 64'b0;

  assign pp00[2*64+1:2*32+1+4] = {((2 * 64 + 1) - (2 * 32 + 1 + 4) + 1) {1'b0}};
  assign pp01[2*64+1:2*33+1+3] = {((2 * 64 + 1) - (2 * 33 + 1 + 3) + 1) {1'b0}};
  assign pp02[2*64+1:2*34+1+3] = {((2 * 64 + 1) - (2 * 34 + 1 + 3) + 1) {1'b0}};
  assign pp03[2*64+1:2*35+1+3] = {((2 * 64 + 1) - (2 * 35 + 1 + 3) + 1) {1'b0}};
  assign pp04[2*64+1:2*36+1+3] = {((2 * 64 + 1) - (2 * 36 + 1 + 3) + 1) {1'b0}};
  assign pp05[2*64+1:2*37+1+3] = {((2 * 64 + 1) - (2 * 37 + 1 + 3) + 1) {1'b0}};
  assign pp06[2*64+1:2*38+1+3] = {((2 * 64 + 1) - (2 * 38 + 1 + 3) + 1) {1'b0}};
  assign pp07[2*64+1:2*39+1+3] = {((2 * 64 + 1) - (2 * 39 + 1 + 3) + 1) {1'b0}};
  assign pp08[2*64+1:2*40+1+3] = {((2 * 64 + 1) - (2 * 40 + 1 + 3) + 1) {1'b0}};
  assign pp09[2*64+1:2*41+1+3] = {((2 * 64 + 1) - (2 * 41 + 1 + 3) + 1) {1'b0}};
  assign pp10[2*64+1:2*42+1+3] = {((2 * 64 + 1) - (2 * 42 + 1 + 3) + 1) {1'b0}};
  assign pp11[2*64+1:2*43+1+3] = {((2 * 64 + 1) - (2 * 43 + 1 + 3) + 1) {1'b0}};
  assign pp12[2*64+1:2*44+1+3] = {((2 * 64 + 1) - (2 * 44 + 1 + 3) + 1) {1'b0}};
  assign pp13[2*64+1:2*45+1+3] = {((2 * 64 + 1) - (2 * 45 + 1 + 3) + 1) {1'b0}};
  assign pp14[2*64+1:2*46+1+3] = {((2 * 64 + 1) - (2 * 46 + 1 + 3) + 1) {1'b0}};
  assign pp15[2*64+1:2*47+1+3] = {((2 * 64 + 1) - (2 * 47 + 1 + 3) + 1) {1'b0}};
  assign pp16[2*64+1:2*48+1+3] = {((2 * 64 + 1) - (2 * 48 + 1 + 3) + 1) {1'b0}};
  assign pp17[2*64+1:2*49+1+3] = {((2 * 64 + 1) - (2 * 49 + 1 + 3) + 1) {1'b0}};
  assign pp18[2*64+1:2*50+1+3] = {((2 * 64 + 1) - (2 * 50 + 1 + 3) + 1) {1'b0}};
  assign pp19[2*64+1:2*51+1+3] = {((2 * 64 + 1) - (2 * 51 + 1 + 3) + 1) {1'b0}};
  assign pp20[2*64+1:2*52+1+3] = {((2 * 64 + 1) - (2 * 52 + 1 + 3) + 1) {1'b0}};
  assign pp21[2*64+1:2*53+1+3] = {((2 * 64 + 1) - (2 * 53 + 1 + 3) + 1) {1'b0}};
  assign pp22[2*64+1:2*54+1+3] = {((2 * 64 + 1) - (2 * 54 + 1 + 3) + 1) {1'b0}};
  assign pp23[2*64+1:2*55+1+3] = {((2 * 64 + 1) - (2 * 55 + 1 + 3) + 1) {1'b0}};
  assign pp24[2*64+1:2*56+1+3] = {((2 * 64 + 1) - (2 * 56 + 1 + 3) + 1) {1'b0}};
  assign pp25[2*64+1:2*57+1+3] = {((2 * 64 + 1) - (2 * 57 + 1 + 3) + 1) {1'b0}};
  assign pp26[2*64+1:2*58+1+3] = {((2 * 64 + 1) - (2 * 58 + 1 + 3) + 1) {1'b0}};
  assign pp27[2*64+1:2*59+1+3] = {((2 * 64 + 1) - (2 * 59 + 1 + 3) + 1) {1'b0}};
  assign pp28[2*64+1:2*60+1+3] = {((2 * 64 + 1) - (2 * 60 + 1 + 3) + 1) {1'b0}};
  assign pp29[2*64+1:2*61+1+3] = {((2 * 64 + 1) - (2 * 61 + 1 + 3) + 1) {1'b0}};
  assign pp30[2*64+1:2*62+1+3] = {((2 * 64 + 1) - (2 * 62 + 1 + 3) + 1) {1'b0}};

  assign pp01[2*00+1:2*00] = {1'b0, rowcin(pp00sel)};
  assign pp02[2*01+1:2*01] = {1'b0, rowcin(pp01sel)};
  assign pp03[2*02+1:2*02] = {1'b0, rowcin(pp02sel)};
  assign pp04[2*03+1:2*03] = {1'b0, rowcin(pp03sel)};
  assign pp05[2*04+1:2*04] = {1'b0, rowcin(pp04sel)};
  assign pp06[2*05+1:2*05] = {1'b0, rowcin(pp05sel)};
  assign pp07[2*06+1:2*06] = {1'b0, rowcin(pp06sel)};
  assign pp08[2*07+1:2*07] = {1'b0, rowcin(pp07sel)};
  assign pp09[2*08+1:2*08] = {1'b0, rowcin(pp08sel)};
  assign pp10[2*09+1:2*09] = {1'b0, rowcin(pp09sel)};
  assign pp11[2*10+1:2*10] = {1'b0, rowcin(pp10sel)};
  assign pp12[2*11+1:2*11] = {1'b0, rowcin(pp11sel)};
  assign pp13[2*12+1:2*12] = {1'b0, rowcin(pp12sel)};
  assign pp14[2*13+1:2*13] = {1'b0, rowcin(pp13sel)};
  assign pp15[2*14+1:2*14] = {1'b0, rowcin(pp14sel)};
  assign pp16[2*15+1:2*15] = {1'b0, rowcin(pp15sel)};
  assign pp17[2*16+1:2*16] = {1'b0, rowcin(pp16sel)};
  assign pp18[2*17+1:2*17] = {1'b0, rowcin(pp17sel)};
  assign pp19[2*18+1:2*18] = {1'b0, rowcin(pp18sel)};
  assign pp20[2*19+1:2*19] = {1'b0, rowcin(pp19sel)};
  assign pp21[2*20+1:2*20] = {1'b0, rowcin(pp20sel)};
  assign pp22[2*21+1:2*21] = {1'b0, rowcin(pp21sel)};
  assign pp23[2*22+1:2*22] = {1'b0, rowcin(pp22sel)};
  assign pp24[2*23+1:2*23] = {1'b0, rowcin(pp23sel)};
  assign pp25[2*24+1:2*24] = {1'b0, rowcin(pp24sel)};
  assign pp26[2*25+1:2*25] = {1'b0, rowcin(pp25sel)};
  assign pp27[2*26+1:2*26] = {1'b0, rowcin(pp26sel)};
  assign pp28[2*27+1:2*27] = {1'b0, rowcin(pp27sel)};
  assign pp29[2*28+1:2*28] = {1'b0, rowcin(pp28sel)};
  assign pp30[2*29+1:2*29] = {1'b0, rowcin(pp29sel)};
  assign pp31[2*30+1:2*30] = {1'b0, rowcin(pp30sel)};
  assign pp32[2*31+1:2*31] = {1'b0, rowcin(pp31sel)};
  assign pp33[2*32+1:2*32] = {1'b0, rowcin(pp32sel)};

  assign pp02[2*01-1:0] = {(2 * 01 - 1 - 0 + 1) {1'b0}};
  assign pp03[2*02-1:0] = {(2 * 02 - 1 - 0 + 1) {1'b0}};
  assign pp04[2*03-1:0] = {(2 * 03 - 1 - 0 + 1) {1'b0}};
  assign pp05[2*04-1:0] = {(2 * 04 - 1 - 0 + 1) {1'b0}};
  assign pp06[2*05-1:0] = {(2 * 05 - 1 - 0 + 1) {1'b0}};
  assign pp07[2*06-1:0] = {(2 * 06 - 1 - 0 + 1) {1'b0}};
  assign pp08[2*07-1:0] = {(2 * 07 - 1 - 0 + 1) {1'b0}};
  assign pp09[2*08-1:0] = {(2 * 08 - 1 - 0 + 1) {1'b0}};
  assign pp10[2*09-1:0] = {(2 * 09 - 1 - 0 + 1) {1'b0}};
  assign pp11[2*10-1:0] = {(2 * 10 - 1 - 0 + 1) {1'b0}};
  assign pp12[2*11-1:0] = {(2 * 11 - 1 - 0 + 1) {1'b0}};
  assign pp13[2*12-1:0] = {(2 * 12 - 1 - 0 + 1) {1'b0}};
  assign pp14[2*13-1:0] = {(2 * 13 - 1 - 0 + 1) {1'b0}};
  assign pp15[2*14-1:0] = {(2 * 14 - 1 - 0 + 1) {1'b0}};
  assign pp16[2*15-1:0] = {(2 * 15 - 1 - 0 + 1) {1'b0}};
  assign pp17[2*16-1:0] = {(2 * 16 - 1 - 0 + 1) {1'b0}};
  assign pp18[2*17-1:0] = {(2 * 17 - 1 - 0 + 1) {1'b0}};
  assign pp19[2*18-1:0] = {(2 * 18 - 1 - 0 + 1) {1'b0}};
  assign pp20[2*19-1:0] = {(2 * 19 - 1 - 0 + 1) {1'b0}};
  assign pp21[2*20-1:0] = {(2 * 20 - 1 - 0 + 1) {1'b0}};
  assign pp22[2*21-1:0] = {(2 * 21 - 1 - 0 + 1) {1'b0}};
  assign pp23[2*22-1:0] = {(2 * 22 - 1 - 0 + 1) {1'b0}};
  assign pp24[2*23-1:0] = {(2 * 23 - 1 - 0 + 1) {1'b0}};
  assign pp25[2*24-1:0] = {(2 * 24 - 1 - 0 + 1) {1'b0}};
  assign pp26[2*25-1:0] = {(2 * 25 - 1 - 0 + 1) {1'b0}};
  assign pp27[2*26-1:0] = {(2 * 26 - 1 - 0 + 1) {1'b0}};
  assign pp28[2*27-1:0] = {(2 * 27 - 1 - 0 + 1) {1'b0}};
  assign pp29[2*28-1:0] = {(2 * 28 - 1 - 0 + 1) {1'b0}};
  assign pp30[2*29-1:0] = {(2 * 29 - 1 - 0 + 1) {1'b0}};
  assign pp31[2*30-1:0] = {(2 * 30 - 1 - 0 + 1) {1'b0}};
  assign pp32[2*31-1:0] = {(2 * 31 - 1 - 0 + 1) {1'b0}};
  assign pp33[2*32-1:0] = {(2 * 32 - 1 - 0 + 1) {1'b0}};

endmodule

module TmpCsa9to2 (  /*AUTOARG*/
  // Outputs
  cout0, cout1, cout2, cout3, cout4, cout5, carry, sum,
  // Inputs
  in0, in1, in2, in3, in4, in5, in6, in7, in8, cin0, cin1, cin2, cin3, cin4,
  cin5
  );

  input in0;
  input in1;
  input in2;
  input in3;
  input in4;
  input in5;
  input in6;
  input in7;
  input in8;
  input cin0;
  input cin1;
  input cin2;
  input cin3;
  input cin4;
  input cin5;

  output cout0;
  output cout1;
  output cout2;
  output cout3;
  output cout4;
  output cout5;
  output carry;
  output sum;

  /*AUTOWIRE*/
  // Beginning of automatic wires (for undeclared instantiated-module outputs)
  wire                  sumi0;                  // From csa0 of TmpCsa3.v
  wire                  sumi1;                  // From csa1 of TmpCsa3.v
  wire                  sumi2;                  // From csa3 of TmpCsa3.v
  // End of automatics

  TmpCsa3 csa0 (  // Outputs
                .out({cout0, sumi0}),
                /*AUTOINST*/
                // Inputs
                .in0                    (in0),
                .in1                    (in1),
                .in2                    (in2));

  TmpCsa3 csa1 (  // Outputs
                .out({cout1, sumi1}),
                // Inputs
                .in0(in3),
                .in1(in4),
                .in2(in5)
                /*AUTOINST*/);

  TmpCsa3 csa3 (  // Outputs
                .out({cout2, sumi2}),
                // Inputs
                .in0(in6),
                .in1(in7),
                .in2(in8)
                /*AUTOINST*/);

  TmpCsa6to2 csa4 (  // Inputs
                   .in0(sumi0),
                   .in1(sumi1),
                   .in2(sumi2),
                   .in3(cin0),
                   .in4(cin1),
                   .in5(cin2),
                   .cin0(cin3),
                   .cin1(cin4),
                   .cin2(cin5),
                   // Outputs
                   .cout0(cout3),
                   .cout1(cout4),
                   .cout2(cout5),
                    /*AUTOINST*/
                   // Outputs
                   .carry              (carry),
                   .sum                (sum));

endmodule

module TmpCsa6to2 (  /*AUTOARG*/
  // Outputs
  cout0, cout1, cout2, carry, sum,
  // Inputs
  in0, in1, in2, in3, in4, in5, cin0, cin1, cin2
  );

  input in0;
  input in1;
  input in2;
  input in3;
  input in4;
  input in5;
  input cin0;
  input cin1;
  input cin2;

  output cout0;
  output cout1;
  output cout2;
  output carry;
  output sum;

  /*AUTOWIRE*/
  // Beginning of automatic wires (for undeclared instantiated-module outputs)
  wire                  sumi0;                  // From csa0 of TmpCsa3.v
  wire                  sumi1;                  // From csa1 of TmpCsa3.v
  // End of automatics

  TmpCsa3 csa0 (// Outputs
                .out({cout0, sumi0}),
                /*AUTOINST*/
                // Inputs
                .in0                    (in0),
                .in1                    (in1),
                .in2                    (in2));

  TmpCsa3 csa1 (// Outputs
                .out({cout1, sumi1}),
                // Inputs
                .in0(in3),
                .in1(in4),
                .in2(in5)
                /*AUTOINST*/);

  TmpCsa4to2 csa3 (// Inputs
                   .in0(sumi0),
                   .in1(sumi1),
                   .in2(cin0),
                   .in3(cin1),
                   .cin(cin2),
                   // Outputs
                   .cout(cout2),
                   /*AUTOINST*/
                   // Outputs
                   .carry              (carry),
                   .sum                (sum));

endmodule

module TmpCsa4to2 (  /*AUTOARG*/
  // Outputs
  cout, carry, sum,
  // Inputs
  in0, in1, in2, in3, cin
  );

  input in0;
  input in1;
  input in2;
  input in3;
  input cin;

  output cout;
  output carry;
  output wire sum;
  wire sumi;

  TmpCsa3 csa0 (  // Outputs
      .out({cout, sumi}),
      // Inputs
      .in0(in0),
      .in1(in1),
      .in2(in2)
  );

  TmpCsa3 csa1 (  // Outputs
      .out({carry, sum}),
      // Inputs
      .in0(in3),
      .in1(sumi),
      .in2(cin)
  );

endmodule

module TmpCsa3 (  /*AUTOARG*/
  // Outputs
  out,
  // Inputs
  in0, in1, in2
  );
  input in0;
  input in1;
  input in2;
  output [1:0] out;
  assign out[0] = in0 ^ in1 ^ in2;
  assign out[1] = (in0 & in1) | (in1 & in2) | (in0 & in2);
endmodule

// Local Variables:
// compile-command: "vlint --brief --nowarn=MULTMF,MODLNM t_math_wallace_mul.v"
// End:
