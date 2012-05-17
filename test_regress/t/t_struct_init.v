// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t;

   //Several simulators don't support this.
   //typedef struct pack2;	// Forward declaration

   typedef struct packed {
      bit	b3;
      bit	b2;
      bit	b1;
      bit	b0;
   } b4_t;

   typedef union packed {
      bit [3:0]	quad0;
      b4_t	quad1;
   } q4_t;

   typedef struct packed {
      bit	msb;
      q4_t	four;
      bit	lsb;
   } pack2_t;

   typedef union packed {
      pack2_t	pack2;
      bit [5:0] pvec;
      // Vector not allowed in packed structure: (Seems cheezy to disallow this)
      //      bit	vec[6];
      //      bit 	vec2d[2][3];
   } pack3_t;

   initial begin
      pack3_t tsu;
      tsu = 6'b100110;
      if (tsu!=6'b100110) $stop;
      if (tsu.pvec!=6'b100110) $stop;
      if (tsu.pack2.msb != 1'b1) $stop;
      if (tsu.pack2.lsb != 1'b0) $stop;
      if (tsu.pack2.four.quad0  != 4'b0011) $stop;
      if (tsu.pack2.four.quad1.b0 != 1'b1) $stop;
      if (tsu.pack2.four.quad1.b1 != 1'b1) $stop;
      if (tsu.pack2.four.quad1.b2 != 1'b0) $stop;
      if (tsu.pack2.four.quad1.b3 != 1'b0) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

   initial begin
      $display("Need init fix\n");
      $stop;
   end
//UNSUP   // Initialization
//UNSUP   initial begin
//UNSUP      b4_t q = '{1'b1, 1'b1, 1'b0, 1'b0};
//UNSUP      if (q != 4'b1100) $stop;
//UNSUP   end
//UNSUP   initial begin
//UNSUP      b4_t q = '{4{1'b1}};	// Repeats the {}
//UNSUP      if (q != 4'b1111) $stop;
//UNSUP   end
//UNSUP   initial begin
//UNSUP      b4_t q = '{b0:1'b1, b2:1'b1, b3:1'b1, b1:1'b0};
//UNSUP      if (q != 4'b1101) $stop;
//UNSUP   end
//UNSUP   initial begin
//UNSUP      b4_t q = '{default:1'b1};
//UNSUP      if (q != 4'b1111) $stop;
//UNSUP      q.b1 = 0;
//UNSUP      if (q != 4'b1101) $stop;
//UNSUP      {q.b3,q.b2} = 2'b10;
//UNSUP      if (q != 4'b1001) $stop;
//UNSUP   end

endmodule
