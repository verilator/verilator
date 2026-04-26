// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define check(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: cyc=%0d got='h%x exp='h%x\n", `__FILE__,`__LINE__, cyc, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t (
    input clk
);

  reg [31:0] cyc = 0;
  reg [6:0] cntA = 0;
  reg [6:0] cntB = 0;
  reg [6:0] cntC = 0;
  reg [6:0] cntD = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc[0]) cntA <= cntA + 7'd1;
    if (cntA[0]) cntB <= cntB + 7'd1;
    if (cntB[0]) cntC <= cntC + 7'd1;
    if (cntC[0]) cntD <= cntD + 7'd1;

    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  sub u_sub(clk, cyc, cntB, cntC);

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

  // Should create decoder
  wire [127:0] cntD_OH = 128'h1 << cntD;
  wire [6:0] cntD_sel =
      (cntD_OH[127] ? 7'd127 : 0) |
      (cntD_OH[126] ? 7'd126 : 0) |
      (cntD_OH[125] ? 7'd125 : 0) |
      (cntD_OH[124] ? 7'd124 : 0) |
      (cntD_OH[123] ? 7'd123 : 0) |
      (cntD_OH[122] ? 7'd122 : 0) |
      (cntD_OH[121] ? 7'd121 : 0) |
      (cntD_OH[120] ? 7'd120 : 0) |
      (cntD_OH[119] ? 7'd119 : 0) |
      (cntD_OH[118] ? 7'd118 : 0) |
      (cntD_OH[117] ? 7'd117 : 0) |
      (cntD_OH[116] ? 7'd116 : 0) |
      (cntD_OH[115] ? 7'd115 : 0) |
      (cntD_OH[114] ? 7'd114 : 0) |
      (cntD_OH[113] ? 7'd113 : 0) |
      (cntD_OH[112] ? 7'd112 : 0) |
      (cntD_OH[111] ? 7'd111 : 0) |
      (cntD_OH[110] ? 7'd110 : 0) |
      (cntD_OH[109] ? 7'd109 : 0) |
      (cntD_OH[108] ? 7'd108 : 0) |
      (cntD_OH[107] ? 7'd107 : 0) |
      (cntD_OH[106] ? 7'd106 : 0) |
      (cntD_OH[105] ? 7'd105 : 0) |
      (cntD_OH[104] ? 7'd104 : 0) |
      (cntD_OH[103] ? 7'd103 : 0) |
      (cntD_OH[102] ? 7'd102 : 0) |
      (cntD_OH[101] ? 7'd101 : 0) |
      (cntD_OH[100] ? 7'd100 : 0) |
      (cntD_OH[99] ? 7'd99 : 0) |
      (cntD_OH[98] ? 7'd98 : 0) |
      (cntD_OH[97] ? 7'd97 : 0) |
      (cntD_OH[96] ? 7'd96 : 0) |
      (cntD_OH[95] ? 7'd95 : 0) |
      (cntD_OH[94] ? 7'd94 : 0) |
      (cntD_OH[93] ? 7'd93 : 0) |
      (cntD_OH[92] ? 7'd92 : 0) |
      (cntD_OH[91] ? 7'd91 : 0) |
      (cntD_OH[90] ? 7'd90 : 0) |
      (cntD_OH[89] ? 7'd89 : 0) |
      (cntD_OH[88] ? 7'd88 : 0) |
      (cntD_OH[87] ? 7'd87 : 0) |
      (cntD_OH[86] ? 7'd86 : 0) |
      (cntD_OH[85] ? 7'd85 : 0) |
      (cntD_OH[84] ? 7'd84 : 0) |
      (cntD_OH[83] ? 7'd83 : 0) |
      (cntD_OH[82] ? 7'd82 : 0) |
      (cntD_OH[81] ? 7'd81 : 0) |
      (cntD_OH[80] ? 7'd80 : 0) |
      (cntD_OH[79] ? 7'd79 : 0) |
      (cntD_OH[78] ? 7'd78 : 0) |
      (cntD_OH[77] ? 7'd77 : 0) |
      (cntD_OH[76] ? 7'd76 : 0) |
      (cntD_OH[75] ? 7'd75 : 0) |
      (cntD_OH[74] ? 7'd74 : 0) |
      (cntD_OH[73] ? 7'd73 : 0) |
      (cntD_OH[72] ? 7'd72 : 0) |
      (cntD_OH[71] ? 7'd71 : 0) |
      (cntD_OH[70] ? 7'd70 : 0) |
      (cntD_OH[69] ? 7'd69 : 0) |
      (cntD_OH[68] ? 7'd68 : 0) |
      (cntD_OH[67] ? 7'd67 : 0) |
      (cntD_OH[66] ? 7'd66 : 0) |
      (cntD_OH[65] ? 7'd65 : 0) |
      (cntD_OH[64] ? 7'd64 : 0) |
      (cntD_OH[63] ? 7'd63 : 0) |
      (cntD_OH[62] ? 7'd62 : 0) |
      (cntD_OH[61] ? 7'd61 : 0) |
      (cntD_OH[60] ? 7'd60 : 0) |
      (cntD_OH[59] ? 7'd59 : 0) |
      (cntD_OH[58] ? 7'd58 : 0) |
      (cntD_OH[57] ? 7'd57 : 0) |
      (cntD_OH[56] ? 7'd56 : 0) |
      (cntD_OH[55] ? 7'd55 : 0) |
      (cntD_OH[54] ? 7'd54 : 0) |
      (cntD_OH[53] ? 7'd53 : 0) |
      (cntD_OH[52] ? 7'd52 : 0) |
      (cntD_OH[51] ? 7'd51 : 0) |
      (cntD_OH[50] ? 7'd50 : 0) |
      (cntD_OH[49] ? 7'd49 : 0) |
      (cntD_OH[48] ? 7'd48 : 0) |
      (cntD_OH[47] ? 7'd47 : 0) |
      (cntD_OH[46] ? 7'd46 : 0) |
      (cntD_OH[45] ? 7'd45 : 0) |
      (cntD_OH[44] ? 7'd44 : 0) |
      (cntD_OH[43] ? 7'd43 : 0) |
      (cntD_OH[42] ? 7'd42 : 0) |
      (cntD_OH[41] ? 7'd41 : 0) |
      (cntD_OH[40] ? 7'd40 : 0) |
      (cntD_OH[39] ? 7'd39 : 0) |
      (cntD_OH[38] ? 7'd38 : 0) |
      (cntD_OH[37] ? 7'd37 : 0) |
      (cntD_OH[36] ? 7'd36 : 0) |
      (cntD_OH[35] ? 7'd35 : 0) |
      (cntD_OH[34] ? 7'd34 : 0) |
      (cntD_OH[33] ? 7'd33 : 0) |
      (cntD_OH[32] ? 7'd32 : 0) |
      (cntD_OH[31] ? 7'd31 : 0) |
      (cntD_OH[30] ? 7'd30 : 0) |
      (cntD_OH[29] ? 7'd29 : 0) |
      (cntD_OH[28] ? 7'd28 : 0) |
      (cntD_OH[27] ? 7'd27 : 0) |
      (cntD_OH[26] ? 7'd26 : 0) |
      (cntD_OH[25] ? 7'd25 : 0) |
      (cntD_OH[24] ? 7'd24 : 0) |
      (cntD_OH[23] ? 7'd23 : 0) |
      (cntD_OH[22] ? 7'd22 : 0) |
      (cntD_OH[21] ? 7'd21 : 0) |
      (cntD_OH[20] ? 7'd20 : 0) |
      (cntD_OH[19] ? 7'd19 : 0) |
      (cntD_OH[18] ? 7'd18 : 0) |
      (cntD_OH[17] ? 7'd17 : 0) |
      (cntD_OH[16] ? 7'd16 : 0) |
      (cntD_OH[15] ? 7'd15 : 0) |
      (cntD_OH[14] ? 7'd14 : 0) |
      (cntD_OH[13] ? 7'd13 : 0) |
      (cntD_OH[12] ? 7'd12 : 0) |
      (cntD_OH[11] ? 7'd11 : 0) |
      (cntD_OH[10] ? 7'd10 : 0) |
      (cntD_OH[9] ? 7'd9 : 0) |
      (cntD_OH[8] ? 7'd8 : 0) |
      (cntD_OH[7] ? 7'd7 : 0) |
      (cntD_OH[6] ? 7'd6 : 0) |
      (cntD_OH[5] ? 7'd5 : 0) |
      (cntD_OH[4] ? 7'd4 : 0) |
      (cntD_OH[3] ? 7'd3 : 0) |
      (cntD_OH[2] ? 7'd2 : 0) |
      (cntD_OH[1] ? 7'd1 : 0) |
      (cntD_OH[0] ? 7'd0 : 0);

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

    `check(twiceCntC, cntC * 7'd2);

    `check(cntD_sel, cntD);
  end

endmodule

module alt;
  reg [6:0] cntC_q;
endmodule

module sub (
  input wire clk,
  input wire [31:0] cyc,
  input wire [6:0] cntB,
  input wire [6:0] cntC
);

  reg [6:0] cntB_q;
  always @(posedge clk) cntB_q <= cntB;

  alt u_alt();
  always @(posedge clk) u_alt.cntC_q <= cntC;

  // Should create decoder
  wire stupidWayToWriteConstOne_B = 1'b0
     + (cntB_q == 7'd127)
     + (cntB_q == 7'd126)
     + (cntB_q == 7'd125)
     + (cntB_q == 7'd124)
     + (cntB_q == 7'd123)
     + (cntB_q == 7'd122)
     + (cntB_q == 7'd121)
     + (cntB_q == 7'd120)
     + (cntB_q == 7'd119)
     + (cntB_q == 7'd118)
     + (cntB_q == 7'd117)
     + (cntB_q == 7'd116)
     + (cntB_q == 7'd115)
     + (cntB_q == 7'd114)
     + (cntB_q == 7'd113)
     + (cntB_q == 7'd112)
     + (cntB_q == 7'd111)
     + (cntB_q == 7'd110)
     + (cntB_q == 7'd109)
     + (cntB_q == 7'd108)
     + (cntB_q == 7'd107)
     + (cntB_q == 7'd106)
     + (cntB_q == 7'd105)
     + (cntB_q == 7'd104)
     + (cntB_q == 7'd103)
     + (cntB_q == 7'd102)
     + (cntB_q == 7'd101)
     + (cntB_q == 7'd100)
     + (cntB_q == 7'd99)
     + (cntB_q == 7'd98)
     + (cntB_q == 7'd97)
     + (cntB_q == 7'd96)
     + (cntB_q == 7'd95)
     + (cntB_q == 7'd94)
     + (cntB_q == 7'd93)
     + (cntB_q == 7'd92)
     + (cntB_q == 7'd91)
     + (cntB_q == 7'd90)
     + (cntB_q == 7'd89)
     + (cntB_q == 7'd88)
     + (cntB_q == 7'd87)
     + (cntB_q == 7'd86)
     + (cntB_q == 7'd85)
     + (cntB_q == 7'd84)
     + (cntB_q == 7'd83)
     + (cntB_q == 7'd82)
     + (cntB_q == 7'd81)
     + (cntB_q == 7'd80)
     + (cntB_q == 7'd79)
     + (cntB_q == 7'd78)
     + (cntB_q == 7'd77)
     + (cntB_q == 7'd76)
     + (cntB_q == 7'd75)
     + (cntB_q == 7'd74)
     + (cntB_q == 7'd73)
     + (cntB_q == 7'd72)
     + (cntB_q == 7'd71)
     + (cntB_q == 7'd70)
     + (cntB_q == 7'd69)
     + (cntB_q == 7'd68)
     + (cntB_q == 7'd67)
     + (cntB_q == 7'd66)
     + (cntB_q == 7'd65)
     + (cntB_q == 7'd64)
     + (cntB_q == 7'd63)
     + (cntB_q == 7'd62)
     + (cntB_q == 7'd61)
     + (cntB_q == 7'd60)
     + (cntB_q == 7'd59)
     + (cntB_q == 7'd58)
     + (cntB_q == 7'd57)
     + (cntB_q == 7'd56)
     + (cntB_q == 7'd55)
     + (cntB_q == 7'd54)
     + (cntB_q == 7'd53)
     + (cntB_q == 7'd52)
     + (cntB_q == 7'd51)
     + (cntB_q == 7'd50)
     + (cntB_q == 7'd49)
     + (cntB_q == 7'd48)
     + (cntB_q == 7'd47)
     + (cntB_q == 7'd46)
     + (cntB_q == 7'd45)
     + (cntB_q == 7'd44)
     + (cntB_q == 7'd43)
     + (cntB_q == 7'd42)
     + (cntB_q == 7'd41)
     + (cntB_q == 7'd40)
     + (cntB_q == 7'd39)
     + (cntB_q == 7'd38)
     + (cntB_q == 7'd37)
     + (cntB_q == 7'd36)
     + (cntB_q == 7'd35)
     + (cntB_q == 7'd34)
     + (cntB_q == 7'd33)
     + (cntB_q == 7'd32)
     + (cntB_q == 7'd31)
     + (cntB_q == 7'd30)
     + (cntB_q == 7'd29)
     + (cntB_q == 7'd28)
     + (cntB_q == 7'd27)
     + (cntB_q == 7'd26)
     + (cntB_q == 7'd25)
     + (cntB_q == 7'd24)
     + (cntB_q == 7'd23)
     + (cntB_q == 7'd22)
     + (cntB_q == 7'd21)
     + (cntB_q == 7'd20)
     + (cntB_q == 7'd19)
     + (cntB_q == 7'd18)
     + (cntB_q <= 7'd17);

  // Should create decoder
  wire stupidWayToWriteConstOne_C = 1'b0
     + (u_alt.cntC_q == 7'd127)
     + (u_alt.cntC_q == 7'd126)
     + (u_alt.cntC_q == 7'd125)
     + (u_alt.cntC_q == 7'd124)
     + (u_alt.cntC_q == 7'd123)
     + (u_alt.cntC_q == 7'd122)
     + (u_alt.cntC_q == 7'd121)
     + (u_alt.cntC_q == 7'd120)
     + (u_alt.cntC_q == 7'd119)
     + (u_alt.cntC_q == 7'd118)
     + (u_alt.cntC_q == 7'd117)
     + (u_alt.cntC_q == 7'd116)
     + (u_alt.cntC_q == 7'd115)
     + (u_alt.cntC_q == 7'd114)
     + (u_alt.cntC_q == 7'd113)
     + (u_alt.cntC_q == 7'd112)
     + (u_alt.cntC_q == 7'd111)
     + (u_alt.cntC_q == 7'd110)
     + (u_alt.cntC_q == 7'd109)
     + (u_alt.cntC_q == 7'd108)
     + (u_alt.cntC_q == 7'd107)
     + (u_alt.cntC_q == 7'd106)
     + (u_alt.cntC_q == 7'd105)
     + (u_alt.cntC_q == 7'd104)
     + (u_alt.cntC_q == 7'd103)
     + (u_alt.cntC_q == 7'd102)
     + (u_alt.cntC_q == 7'd101)
     + (u_alt.cntC_q == 7'd100)
     + (u_alt.cntC_q == 7'd99)
     + (u_alt.cntC_q == 7'd98)
     + (u_alt.cntC_q == 7'd97)
     + (u_alt.cntC_q == 7'd96)
     + (u_alt.cntC_q == 7'd95)
     + (u_alt.cntC_q == 7'd94)
     + (u_alt.cntC_q == 7'd93)
     + (u_alt.cntC_q == 7'd92)
     + (u_alt.cntC_q == 7'd91)
     + (u_alt.cntC_q == 7'd90)
     + (u_alt.cntC_q == 7'd89)
     + (u_alt.cntC_q == 7'd88)
     + (u_alt.cntC_q == 7'd87)
     + (u_alt.cntC_q == 7'd86)
     + (u_alt.cntC_q == 7'd85)
     + (u_alt.cntC_q == 7'd84)
     + (u_alt.cntC_q == 7'd83)
     + (u_alt.cntC_q == 7'd82)
     + (u_alt.cntC_q == 7'd81)
     + (u_alt.cntC_q == 7'd80)
     + (u_alt.cntC_q == 7'd79)
     + (u_alt.cntC_q == 7'd78)
     + (u_alt.cntC_q == 7'd77)
     + (u_alt.cntC_q == 7'd76)
     + (u_alt.cntC_q == 7'd75)
     + (u_alt.cntC_q == 7'd74)
     + (u_alt.cntC_q == 7'd73)
     + (u_alt.cntC_q == 7'd72)
     + (u_alt.cntC_q == 7'd71)
     + (u_alt.cntC_q == 7'd70)
     + (u_alt.cntC_q == 7'd69)
     + (u_alt.cntC_q == 7'd68)
     + (u_alt.cntC_q == 7'd67)
     + (u_alt.cntC_q == 7'd66)
     + (u_alt.cntC_q == 7'd65)
     + (u_alt.cntC_q == 7'd64)
     + (u_alt.cntC_q == 7'd63)
     + (u_alt.cntC_q == 7'd62)
     + (u_alt.cntC_q == 7'd61)
     + (u_alt.cntC_q == 7'd60)
     + (u_alt.cntC_q == 7'd59)
     + (u_alt.cntC_q == 7'd58)
     + (u_alt.cntC_q == 7'd57)
     + (u_alt.cntC_q == 7'd56)
     + (u_alt.cntC_q == 7'd55)
     + (u_alt.cntC_q == 7'd54)
     + (u_alt.cntC_q == 7'd53)
     + (u_alt.cntC_q == 7'd52)
     + (u_alt.cntC_q == 7'd51)
     + (u_alt.cntC_q == 7'd50)
     + (u_alt.cntC_q == 7'd49)
     + (u_alt.cntC_q == 7'd48)
     + (u_alt.cntC_q == 7'd47)
     + (u_alt.cntC_q == 7'd46)
     + (u_alt.cntC_q == 7'd45)
     + (u_alt.cntC_q == 7'd44)
     + (u_alt.cntC_q == 7'd43)
     + (u_alt.cntC_q == 7'd42)
     + (u_alt.cntC_q == 7'd41)
     + (u_alt.cntC_q == 7'd40)
     + (u_alt.cntC_q == 7'd39)
     + (u_alt.cntC_q == 7'd38)
     + (u_alt.cntC_q == 7'd37)
     + (u_alt.cntC_q == 7'd36)
     + (u_alt.cntC_q == 7'd35)
     + (u_alt.cntC_q == 7'd34)
     + (u_alt.cntC_q == 7'd33)
     + (u_alt.cntC_q == 7'd32)
     + (u_alt.cntC_q == 7'd31)
     + (u_alt.cntC_q == 7'd30)
     + (u_alt.cntC_q == 7'd29)
     + (u_alt.cntC_q == 7'd28)
     + (u_alt.cntC_q == 7'd27)
     + (u_alt.cntC_q == 7'd26)
     + (u_alt.cntC_q == 7'd25)
     + (u_alt.cntC_q == 7'd24)
     + (u_alt.cntC_q == 7'd23)
     + (u_alt.cntC_q == 7'd22)
     + (u_alt.cntC_q == 7'd21)
     + (u_alt.cntC_q == 7'd20)
     + (u_alt.cntC_q == 7'd19)
     + (u_alt.cntC_q == 7'd18)
     + (u_alt.cntC_q <= 7'd17);

  always @(posedge clk) begin
    `check(stupidWayToWriteConstOne_B, 1'b1);

    `check(stupidWayToWriteConstOne_C, 1'b1);
  end

endmodule
