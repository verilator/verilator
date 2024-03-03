// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Justin Yao Du.
// SPDX-License-Identifier: CC0-1.0

typedef logic [7:0] Word;
typedef logic [255:0] BigItem;

module shuffler
  (
    input logic clk,
    input logic reset_l,
    output logic odd,
    output logic [255:0][7:0] shuffle
   );

   Word ctr;
   assign odd = ctr[0];

   always_ff @(posedge clk) begin
      if (!reset_l) begin
         ctr <= 0;
      end
      else begin
         ctr <= ctr + 1;
      end
   end

   for (genvar i = 0; i < 256; i++) always_comb begin
       shuffle[i] = Word'(i) - ctr;
   end

   for (genvar i = 0; i < 256; i++) begin
      assert property (@(posedge clk) shuffle[ctr + Word'(i)] == i);
   end
endmodule

interface big_port();
   BigItem big;

   function automatic BigItem get_big();
      return big;
   endfunction

   modport reader(import get_big);
endinterface

module foo (
   input clk,
   input reset_l,
   big_port.reader big);

   logic odd;
   Word[255 : 0] shuffle;
   shuffler fifo (
       .clk,
       .reset_l,
       .odd,
       .shuffle
   );

   BigItem bigs[256];
   for (genvar i = 0; i < 256; i++) always_comb begin
      bigs[i] = odd ? big.get_big() : 0;
   end
endmodule

module t (/*AUTOARG*/
   // Inputs
   clk, reset_l
   );

   input clk;
   input reset_l;

   big_port big();

   foo foo (
        .clk,
        .reset_l,
        .big);

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
