// DESCRIPTION: Verilator: Verilog Test module for Issue#1609
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Julien Margetts.

module t (/*AUTOARG*/ out, out2, in );

   input      [9:0] in;
   output reg [3:0] out;
   output reg [3:0] out2;

    // Should be no latch here since the input space is fully covered

   always @* begin
      casez (in)
      10'b0000000000 : out = 4'h0;
      10'b?????????1 : out = 4'h0;
      10'b????????10 : out = 4'h1;
      10'b???????100 : out = 4'h2;
      10'b??????1000 : out = 4'h3;
      10'b?????10000 : out = 4'h4;
      10'b????100000 : out = 4'h5;
      10'b???1000000 : out = 4'h6;
      10'b??10000000 : out = 4'h7;
      10'b?100000000 : out = 4'h8;
      10'b1000000000 : out = 4'h9;
      endcase
   end

   // Should detect a latch here since not all paths assign
   // BUT we don't because warnOff(LATCH) is set for any always containing a
   // complex case statement

   always @* begin
      casez (in)
      10'b0000000000 : out2 = 4'h0;
      10'b?????????1 : out2 = 4'h0;
      10'b????????10 : out2 = 4'h1;
      10'b???????100 : out2 = 4'h2;
      10'b??????1000 : out2 = 4'h3;
      10'b?????10000 : /* No assignement */ ;
      10'b????100000 : out2 = 4'h5;
      10'b???1000000 : out2 = 4'h6;
      10'b??10000000 : out2 = 4'h7;
      10'b?100000000 : out2 = 4'h8;
      10'b1000000000 : out2 = 4'h9;
      endcase
   end

endmodule
