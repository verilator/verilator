// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   localparam NO = 10;  // number of access events

   // packed structures
   struct packed {
      logic       e0;
      logic [1:0] e1;
      logic [3:0] e2;
      logic [7:0] e3;
   } struct_bg;  // big endian structure
   /* verilator lint_off LITENDIAN */
   struct packed {
      logic       e0;
      logic [0:1] e1;
      logic [0:3] e2;
      logic [0:7] e3;
   } struct_lt;  // little endian structure
   /* verilator lint_on LITENDIAN */

   localparam WS = 15;  // $bits(struct_bg)

   integer cnt = 0;

   // event counter
   always @ (posedge clk)
   begin
      cnt <= cnt + 1;
   end

   // finish report
   always @ (posedge clk)
   if ((cnt[30:2]==NO) && (cnt[1:0]==2'd0)) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

   // big endian
   always @ (posedge clk)
   if (cnt[1:0]==2'd0) begin
      // initialize to defaaults (all bits to 0)
      if      (cnt[30:2]==0)  struct_bg <= '0;
      else if (cnt[30:2]==1)  struct_bg <= '0;
      else if (cnt[30:2]==2)  struct_bg <= '0;
      else if (cnt[30:2]==3)  struct_bg <= '0;
      else if (cnt[30:2]==4)  struct_bg <= '0;
      else if (cnt[30:2]==5)  struct_bg <= '0;
   end else if (cnt[1:0]==2'd1) begin
      // write value to structure
      if      (cnt[30:2]==0)  begin end
      else if (cnt[30:2]==1)  struct_bg    <= '1;
      else if (cnt[30:2]==2)  struct_bg.e0 <= '1;
      else if (cnt[30:2]==3)  struct_bg.e1 <= '1;
      else if (cnt[30:2]==4)  struct_bg.e2 <= '1;
      else if (cnt[30:2]==5)  struct_bg.e3 <= '1;
   end else if (cnt[1:0]==2'd2) begin
      // check structure value
      if      (cnt[30:2]==0)  begin if (struct_bg !== 15'b000000000000000) begin $display("%b", struct_bg); $stop(); end end
      else if (cnt[30:2]==1)  begin if (struct_bg !== 15'b111111111111111) begin $display("%b", struct_bg); $stop(); end end
      else if (cnt[30:2]==2)  begin if (struct_bg !== 15'b100000000000000) begin $display("%b", struct_bg); $stop(); end end
      else if (cnt[30:2]==3)  begin if (struct_bg !== 15'b011000000000000) begin $display("%b", struct_bg); $stop(); end end
      else if (cnt[30:2]==4)  begin if (struct_bg !== 15'b000111100000000) begin $display("%b", struct_bg); $stop(); end end
      else if (cnt[30:2]==5)  begin if (struct_bg !== 15'b000000011111111) begin $display("%b", struct_bg); $stop(); end end
   end else if (cnt[1:0]==2'd3) begin
      // read value from structure (not a very good test for now)
      if      (cnt[30:2]==0)  begin if (struct_bg    !== {WS{1'b0}}) $stop(); end
      else if (cnt[30:2]==1)  begin if (struct_bg    !== {WS{1'b1}}) $stop(); end
      else if (cnt[30:2]==2)  begin if (struct_bg.e0 !== { 1{1'b1}}) $stop(); end
      else if (cnt[30:2]==3)  begin if (struct_bg.e1 !== { 2{1'b1}}) $stop(); end
      else if (cnt[30:2]==4)  begin if (struct_bg.e2 !== { 4{1'b1}}) $stop(); end
      else if (cnt[30:2]==5)  begin if (struct_bg.e3 !== { 8{1'b1}}) $stop(); end
   end

   // little endian
   always @ (posedge clk)
   if (cnt[1:0]==2'd0) begin
      // initialize to defaaults (all bits to 0)
      if      (cnt[30:2]==0)  struct_lt <= '0;
      else if (cnt[30:2]==1)  struct_lt <= '0;
      else if (cnt[30:2]==2)  struct_lt <= '0;
      else if (cnt[30:2]==3)  struct_lt <= '0;
      else if (cnt[30:2]==4)  struct_lt <= '0;
      else if (cnt[30:2]==5)  struct_lt <= '0;
   end else if (cnt[1:0]==2'd1) begin
      // write value to structure
      if      (cnt[30:2]==0)  begin end
      else if (cnt[30:2]==1)  struct_lt    <= '1;
      else if (cnt[30:2]==2)  struct_lt.e0 <= '1;
      else if (cnt[30:2]==3)  struct_lt.e1 <= '1;
      else if (cnt[30:2]==4)  struct_lt.e2 <= '1;
      else if (cnt[30:2]==5)  struct_lt.e3 <= '1;
   end else if (cnt[1:0]==2'd2) begin
      // check structure value
      if      (cnt[30:2]==0)  begin if (struct_lt !== 15'b000000000000000) begin $display("%b", struct_lt); $stop(); end end
      else if (cnt[30:2]==1)  begin if (struct_lt !== 15'b111111111111111) begin $display("%b", struct_lt); $stop(); end end
      else if (cnt[30:2]==2)  begin if (struct_lt !== 15'b100000000000000) begin $display("%b", struct_lt); $stop(); end end
      else if (cnt[30:2]==3)  begin if (struct_lt !== 15'b011000000000000) begin $display("%b", struct_lt); $stop(); end end
      else if (cnt[30:2]==4)  begin if (struct_lt !== 15'b000111100000000) begin $display("%b", struct_lt); $stop(); end end
      else if (cnt[30:2]==5)  begin if (struct_lt !== 15'b000000011111111) begin $display("%b", struct_lt); $stop(); end end
   end else if (cnt[1:0]==2'd3) begin
      // read value from structure (not a very good test for now)
      if      (cnt[30:2]==0)  begin if (struct_lt    !== {WS{1'b0}}) $stop(); end
      else if (cnt[30:2]==1)  begin if (struct_lt    !== {WS{1'b1}}) $stop(); end
      else if (cnt[30:2]==2)  begin if (struct_lt.e0 !== { 1{1'b1}}) $stop(); end
      else if (cnt[30:2]==3)  begin if (struct_lt.e1 !== { 2{1'b1}}) $stop(); end
      else if (cnt[30:2]==4)  begin if (struct_lt.e2 !== { 4{1'b1}}) $stop(); end
      else if (cnt[30:2]==5)  begin if (struct_lt.e3 !== { 8{1'b1}}) $stop(); end
   end

endmodule
