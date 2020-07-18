// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // counters
   int cnt;
   int cnt_bit ;
   int cnt_byte;
   int cnt_int ;
   int cnt_ar1d;
   int cnt_ar2d;

   // sizes
   int siz_bit ;
   int siz_byte;
   int siz_int ;
   int siz_ar1d;
   int siz_ar2d;

   // add all counters
   assign cnt = cnt_bit + cnt_byte + cnt_int + cnt_ar1d + cnt_ar2d;

   // finish report
   always @ (posedge clk)
   if (cnt == 5) begin
      if (siz_bit  !=  1)  $stop();
      if (siz_byte !=  8)  $stop();
      if (siz_int  != 32)  $stop();
      if (siz_ar1d != 24)  $stop();
      if (siz_ar2d != 16)  $stop();
   end else if (cnt > 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

   // instances with various types
   mod_typ #(.TYP (bit           )) mod_bit  (clk, cnt_bit [ 1-1:0], siz_bit );
   mod_typ #(.TYP (byte          )) mod_byte (clk, cnt_byte[ 8-1:0], siz_byte);
   mod_typ #(.TYP (int           )) mod_int  (clk, cnt_int [32-1:0], siz_int );
   mod_typ #(.TYP (bit [23:0]    )) mod_ar1d (clk, cnt_ar1d[24-1:0], siz_ar1d);
   mod_typ #(.TYP (bit [3:0][3:0])) mod_ar2d (clk, cnt_ar2d[16-1:0], siz_ar2d);

   // double types
   mod_typ2 #(.WIDTH1(3), .WIDTH2(3), .TYP1(bit [2:0])) mod2_3_3();
   mod_typ2 #(.WIDTH1(3), .WIDTH2(5), .TYP1(bit [2:0]), .TYP2(bit[4:0])) mod2_3_5();

endmodule : t


module mod_typ #(
   parameter type TYP = byte
)(
   input  logic clk,
   output TYP   cnt,
   output int   siz
);

   initial cnt = 0;

   always @ (posedge clk)
     cnt <= cnt + 1;

   assign siz = $bits (cnt);

endmodule

module mod_typ2
  #(
    parameter int WIDTH1 = 0,
    parameter int WIDTH2 = WIDTH1,
    parameter type TYP1 = byte,
    // Below we need to imply that TYP2 is a type
    TYP2 = TYP1
    )();

   TYP1 t1;
   TYP2 t2;

   initial begin
      if ($bits(t1) != WIDTH1) $stop;
      if ($bits(t2) != WIDTH2) $stop;
   end

endmodule
