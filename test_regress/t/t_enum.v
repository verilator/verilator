// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

typedef enum logic [4:0]
     {
      BIT0 = 5'd0,
      BIT1 = 5'd1,
      BIT2 = 5'd2
      } three_t;

module t (/*AUTOARG*/);

   localparam FIVE = 5;

   enum { e0,
	  e1,
	  e3=3,
	  e5=FIVE,
	  e10_[2] = 10,
	  e20_[5:7] = 25,
	  e20_z,
	  e30_[7:5] = 30,
	  e30_z
	  } EN;

   enum {
	 z5 = e5
	 } ZN;

   typedef enum [2:0] { ONES=~0 } three_t;
   three_t three = ONES;

   var logic [ONES:0] sized_based_on_enum;

   var enum logic [3:0]  { QINVALID='1, QSEND={2'b0,2'h0}, QOP={2'b0,2'h1}, QCL={2'b0,2'h2},
			   QPR={2'b0,2'h3 }, QACK, QRSP } inv;

   initial begin
      if (e0 !== 0) $stop;
      if (e1 !== 1) $stop;
      if (e3 !== 3) $stop;
      if (e5 !== 5) $stop;
      if (e10_0 !== 10) $stop;
      if (e10_1 !== 11) $stop;
      if (e20_5 !== 25) $stop;
      if (e20_6 !== 26) $stop;
      if (e20_7 !== 27) $stop;
      if (e20_z !== 28) $stop;
      if (e30_7 !== 30) $stop;
      if (e30_6 !== 31) $stop;
      if (e30_5 !== 32) $stop;
      if (e30_z !== 33) $stop;

      if (z5 !== 5) $stop;

      if (three != 3'b111) $stop;

      if ($bits(sized_based_on_enum) != 8) $stop;
      if ($bits(three_t) != 3) $stop;

      if (FIVE[BIT0] != 1'b1) $stop;
      if (FIVE[BIT1] != 1'b0) $stop;
      if (FIVE[BIT2] != 1'b1) $stop;

      if (QINVALID != 15) $stop;
      if (QSEND    !=  0) $stop;
      if (QOP      !=  1) $stop;
      if (QCL      !=  2) $stop;
      if (QPR      !=  3) $stop;
      if (QACK     !=  4) $stop;
      if (QRSP     !=  5) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
