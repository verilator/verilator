// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   logic [15:0] i16;
   logic [15:0] o16;
   logic [31:0] i32;
   logic [31:0] o32;
   logic [63:0] i64;
   logic [63:0] o64;

   always_comb begin
      o16 = {<<4{i16}};
      o32 = {<<4{i32}};
      o64 = {<<4{i64}};
   end

   initial begin
      i16 = 16'hfade;
      i32 = 32'hcafefade;
      i64 = 64'hdeaddeedcafefade;
      #100ns;
      $display("o16=0x%h i16=0x%h", o16, i16);
      if (o16 != 16'hEDAF) $stop;
      $display("o32=0x%h i32=0x%h", o32, i32);
      if (o32 != 32'hEDAFEFAC) $stop;
      $display("o64=0x%h i64=0x%h", o64, i64);
      if (o64 != 64'hEDAFEFACDEEDDAED) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
