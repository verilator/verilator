// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2005 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  wire [7:0] bitout;
  reg  [7:0] allbits;
  reg  [7:0]  onebit;
  reg  [8:0] onebitbad;  // Wrongly sized

  sub sub [7:0] (allbits, onebitbad, bitout);

  // This is ok.
  wire [9:8] b;
  wire [1:0] c;
  sub sub2 [9:8] (allbits,b,c);

  // Multi-dimensional, 6 elements
  reg  [6:0] sixbitbad;  // Wrongly sized
  wire [5:0] sixbitout;
  sub sub3 [1:0][2:0] (allbits, sixbitbad, sixbitout);

  // Unpacked connection with fewer unpacked dimensions than the instance array
  reg  onebits2[1:0];
  wire [5:0] sixbitout2;
  sub sub5 [1:0][2:0] (allbits, onebits2, sixbitout2);

endmodule

module sub (input [7:0] allbits, input onebit, output bitout);
  assign bitout = onebit ^ (^ allbits);
endmodule
