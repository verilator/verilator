// DESCRIPTION: Verilator: Verilog Test module
//
// A test case for struct signal bit selection.
//
// This test is to check that bit selection of multi-dimensional signal inside
// of a packed struct works. Currently +: and -: blow up with packed structs.
//
// This file ONLY is placed into the Public Domain, for any use, without
// warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

// Test IEEE 1800-2023 concat bit selects, function bit selects, method bit selects

class Cls;
   static function logic [15:0] valf1ed();
      return 16'hf1ed;
   endfunction
endclass

module t(/*AUTOARG*/);

   Cls c;

   int q[$];

   logic [7:0] aa;
   logic [7:0] bb;
   logic [7:0] s8;
   logic       s1;

   function logic [15:0] valf0ed();
      return 16'hf0ed;
   endfunction

   initial begin
      aa = 8'haa;
      bb = 8'hbb;

      s1 = {aa,bb}[8];
      `checkh(s1, 1'b0);
      s1 = {aa,bb}[9];
      `checkh(s1, 1'b1);
      s8 = {aa,bb}[11:4];
      `checkh(s8, 8'hab);
      s8 = {aa,bb}[4+:8];
      `checkh(s8, 8'hab);
      s8 = {aa,bb}[11-:8];
      `checkh(s8, 8'hab);

      s1 = valf0ed()[4];
      `checkh(s1, 1'b0);
      s1 = valf0ed()[5];
      `checkh(s1, 1'b1);
      s8 = valf0ed()[11:4];
      `checkh(s8, 8'h0e);
      s8 = valf0ed()[4+:8];
      `checkh(s8, 8'h0e);
      s8 = valf0ed()[11-:8];
      `checkh(s8, 8'h0e);

      c = new;
      s1 = c.valf1ed()[4];
      `checkh(s1, 1'b0);
      s1 = c.valf1ed()[5];
      `checkh(s1, 1'b1);
      s8 = c.valf1ed()[11:4];
      `checkh(s8, 8'h1e);
      s8 = c.valf1ed()[4+:8];
      `checkh(s8, 8'h1e);
      s8 = c.valf1ed()[11-:8];
      `checkh(s8, 8'h1e);

      q.push_front(32'h10ef);
      s1 = q.sum()[4];
      `checkh(s1, 1'b0);
      s1 = q.sum()[5];
      `checkh(s1, 1'b1);
      s8 = q.sum()[11:4];
      `checkh(s8, 8'h0e);
      s8 = q.sum()[4+:8];
      `checkh(s8, 8'h0e);
      s8 = q.sum()[11-:8];
      `checkh(s8, 8'h0e);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
