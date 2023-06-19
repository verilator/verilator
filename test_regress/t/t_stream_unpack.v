// DESCRIPTION: Verilator: Verilog Test module
// Ref. to  IEEE Std 1800-2017  11.4.14 & A.8.1
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Victor Besyakov.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // 1D packed array into concatenation
   logic [32-1:0] concat_din;
   logic  [8-1:0]                concat4_dout3, concat4_dout2, concat4_dout1, concat4_dout0;  // same size
   logic  [8-1:0]                concat3_dout3, concat3_dout2, concat3_dout1               ;  // smaller
   logic  [8-1:0] concat5_dout4, concat5_dout3, concat5_dout2, concat5_dout1, concat5_dout0;  // larger

   // 2D packed array into unpacked array
   /* verilator lint_off ASCRANGE */
   logic [0:4-1][8-1:0] packed_siz_din;
   logic [0:4-1][8-1:0] packed_asc_din;
   /* verilator lint_on ASCRANGE */
   logic [4-1:0][8-1:0] packed_des_din;
   logic        [8-1:0] unpacked_siz_dout [4];
   logic        [8-1:0] unpacked_asc_dout [0:4-1];
   logic        [8-1:0] unpacked_des_dout [4-1:0];

   // 2D unpacked array into packed array
   logic        [8-1:0] unpacked_siz_din [4];
   logic        [8-1:0] unpacked_asc_din [0:4-1];
   logic        [8-1:0] unpacked_des_din [4-1:0];
   /* verilator lint_off ASCRANGE */
   logic [0:4-1][8-1:0] packed_siz_dout;
   logic [0:4-1][8-1:0] packed_asc_dout;
   /* verilator lint_on ASCRANGE */
   logic [4-1:0][8-1:0] packed_des_dout;

   // 2D packed array into queue
   logic        [8-1:0] packed_siz_queue_dout [$];
   logic        [8-1:0] packed_asc_queue_dout [$];
   logic        [8-1:0] packed_des_queue_dout [$];
   // 2D unpacked array into queue
   logic        [8-1:0] unpacked_siz_queue_dout [$];
   logic        [8-1:0] unpacked_asc_queue_dout [$];
   logic        [8-1:0] unpacked_des_queue_dout [$];


   integer cyc = 1;

   always_comb begin
      // 1D packed array into concatenation
      {>>{               concat4_dout3, concat4_dout2, concat4_dout1, concat4_dout0}} = concat_din;
      /* verilator lint_off WIDTHTRUNC */
      {>>{               concat3_dout3, concat3_dout2, concat3_dout1               }} = concat_din;
      /* verilator lint_on WIDTHTRUNC */
      /* verilator lint_off WIDTHEXPAND */
      {>>{concat5_dout4, concat5_dout3, concat5_dout2, concat5_dout1, concat5_dout0}} = concat_din;
      /* verilator lint_on WIDTHEXPAND */
      // 2D packed array into unpacked array
      {>>{unpacked_siz_dout}} = packed_asc_din;
      {>>{unpacked_asc_dout}} = packed_asc_din;
      {>>{unpacked_des_dout}} = packed_des_din;
      // 2D unpacked array into packed array
      {>>{packed_siz_dout}} = unpacked_siz_din;
      {>>{packed_asc_dout}} = unpacked_asc_din;
      {>>{packed_des_dout}} = unpacked_des_din;
      // 2D packed array into queue
      {>>{packed_siz_queue_dout}} = packed_siz_din;
      {>>{packed_asc_queue_dout}} = packed_asc_din;
      {>>{packed_des_queue_dout}} = packed_des_din;
      // 2D unpacked array into queue
      {>>{unpacked_siz_queue_dout}} = unpacked_siz_din;
      {>>{unpacked_asc_queue_dout}} = unpacked_asc_din;
      {>>{unpacked_des_queue_dout}} = unpacked_des_din;
   end

   always @(posedge clk) begin
      if (cyc != 0) begin
         cyc <= cyc + 1;

         if (cyc == 1) begin
            // 1D packed array into concatenation
            concat_din <= 32'h76543210;
            // 2D packed array into unpacked array
            packed_siz_din <= '{8'h01, 8'h23, 8'h45, 8'h67};
            packed_asc_din <= '{8'h01, 8'h23, 8'h45, 8'h67};
            packed_des_din <= '{8'h76, 8'h54, 8'h32, 8'h10};
            // 2D unpacked array into packed array
            unpacked_siz_din <= '{8'h01, 8'h23, 8'h45, 8'h67};
            unpacked_asc_din <= '{8'h01, 8'h23, 8'h45, 8'h67};
            unpacked_des_din <= '{8'h76, 8'h54, 8'h32, 8'h10};
         end

         if (cyc == 2) begin
            // 1D packed array into concatenation (same size)
            if (concat4_dout0 != 8'h10) $stop;
            if (concat4_dout1 != 8'h32) $stop;
            if (concat4_dout2 != 8'h54) $stop;
            if (concat4_dout3 != 8'h76) $stop;
            // 1D packed array into concatenation (smaller)
            if (concat3_dout1 != 8'h32) $stop;
            if (concat3_dout2 != 8'h54) $stop;
            if (concat3_dout3 != 8'h76) $stop;
            // 1D packed array into concatenation (larger)
            if (concat5_dout0 != 8'h00) $stop;
            if (concat5_dout1 != 8'h10) $stop;
            if (concat5_dout2 != 8'h32) $stop;
            if (concat5_dout3 != 8'h54) $stop;
            if (concat5_dout4 != 8'h76) $stop;
            // 2D packed array into unpacked array
            if (unpacked_siz_dout != '{8'h01, 8'h23, 8'h45, 8'h67}) $stop;
            if (unpacked_asc_dout != '{8'h01, 8'h23, 8'h45, 8'h67}) $stop;
            if (unpacked_des_dout != '{8'h76, 8'h54, 8'h32, 8'h10}) $stop;
            // 2D unpacked array into packed array
            if (packed_siz_dout != '{8'h01, 8'h23, 8'h45, 8'h67}) $stop;
            if (packed_asc_dout != '{8'h01, 8'h23, 8'h45, 8'h67}) $stop;
            if (packed_des_dout != '{8'h76, 8'h54, 8'h32, 8'h10}) $stop;
            // 2D packed array into queue
            if (packed_siz_queue_dout != '{8'h01, 8'h23, 8'h45, 8'h67}) $stop;
            if (packed_asc_queue_dout != '{8'h01, 8'h23, 8'h45, 8'h67}) $stop;
            if (packed_des_queue_dout != '{8'h76, 8'h54, 8'h32, 8'h10}) $stop;
            // 2D unpacked array into queue
            if (unpacked_siz_queue_dout != '{8'h01, 8'h23, 8'h45, 8'h67}) $stop;
            if (unpacked_asc_queue_dout != '{8'h01, 8'h23, 8'h45, 8'h67}) $stop;
            if (unpacked_des_queue_dout != '{8'h76, 8'h54, 8'h32, 8'h10}) $stop;
         end

         if (cyc == 3) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule
