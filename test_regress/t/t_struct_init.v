// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t;

   //Several simulators don't support this.
   //typedef struct pack2;	// Forward declaration

   typedef struct packed { // [3:0]
      bit	b3;
      bit	b2;
      bit	b1;
      bit	b0;
   } b4_t;

   typedef struct packed { // [3:0]
      b4_t	x1;
      b4_t	x0;
   } b4x2_t;

   typedef union packed { // [3:0]
      bit [3:0]	quad0;
      b4_t	quad1;
   } q4_t;

   typedef struct packed { // [5:0]
      bit	msb;
      q4_t	four;
      bit	lsb;
   } pack2_t;

   typedef union packed { // [5:0]
      pack2_t	pack2;
      bit [6:1] pvec;
      // Vector not allowed in packed structure, per spec:
      //      bit	vec[6];
      //      bit 	vec2d[2][3];
   } pack3_t;

   const b4_t b4_const_a = '{1'b1, 1'b0, 1'b0, 1'b1};

   pack2_t arr[2];

   initial begin
      pack3_t tsu;
      tsu = 6'b110110;
      //          543210
      if (tsu!=6'b110110) $stop;
      if (tsu[5:4]!=2'b11) $stop;
      if (tsu[5:4] == tsu[1:0]) $stop;  // Not a good extraction test if LSB subtraction doesn't matter
      if (tsu.pvec!=6'b110110) $stop;
      if (tsu.pvec[6:5]!=2'b11) $stop;
      if (tsu.pack2[5:1] != 5'b11011) $stop;
      if (tsu.pack2.msb != 1'b1) $stop;
      if (tsu.pack2.lsb != 1'b0) $stop;
      if (tsu.pack2.four.quad0  != 4'b1011) $stop;
      if (tsu.pack2.four.quad1.b0 != 1'b1) $stop;
      if (tsu.pack2.four.quad1.b1 != 1'b1) $stop;
      if (tsu.pack2.four.quad1.b2 != 1'b0) $stop;
      if (tsu.pack2.four.quad1.b3 != 1'b1) $stop;
      //
      arr[0] = 6'b101010;
      arr[1] = 6'b010101;
      if (arr[0].four !== 4'b0101) $stop;
      if (arr[1].four !== 4'b1010) $stop;
      //
      // Initialization
      begin
	 b4_t q = '{1'b1, 1'b1, 1'b0, 1'b0};
	 if (q != 4'b1100) $stop;
      end
      begin
	 b4_t q = '{3{1'b1}, 1'b0};
	 if (q != 4'b1110) $stop;
      end
      begin
	 b4_t q = '{4{1'b1}};	// Repeats the {}
	 if (q != 4'b1111) $stop;
      end
      begin
	 b4x2_t m = '{4'b1001, '{1'b1, 1'b0, 1'b1, 1'b1}};
	 if (m != 8'b10011011) $stop;
      end
      begin
	 b4_t q = '{default:1'b1};
	 if (q != 4'b1111) $stop;
      end
      begin
	 b4_t q = '{b0:1'b1, b2:1'b1, b3:1'b1, b1:1'b0};
	 if (q != 4'b1101) $stop;
      end
      begin
	 b4_t q = '{b2:1'b0, default:1'b1};
	 if (q != 4'b1011) $stop;
      end

      if (b4_const_a != 4'b1001) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
