// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test tagged union declaration, expressions, and member access
// IEEE 1800-2023 Sections 7.3.2, 11.9

module t;

   // Basic tagged union with void and int (IEEE example)
   typedef union tagged {
      void Invalid;
      int Valid;
   } VInt;

   // Tagged union with multiple data types
   typedef union tagged packed {
      void      Invalid;
      int       IntVal;
      shortint  ShortVal;
      longint   LongVal;
      byte      ByteVal;
      bit       BitVal;
      logic     LogicVal;
      bit [7:0] Byte8;
      bit [15:0] Word16;
      bit [31:0] Word32;
   } MultiType;

   // Tagged union with nested struct (IEEE example)
   typedef union tagged {
      struct {
         bit [4:0] reg1, reg2, regd;
      } Add;
      union tagged {
         bit [9:0] JmpU;
         struct {
            bit [1:0] cc;
            bit [9:0] addr;
         } JmpC;
      } Jmp;
   } Instr;

   VInt vi1, vi2;
   MultiType mt;
   Instr instr;

   initial begin
      // Test 1: Basic void member
      vi1 = tagged Invalid;
      vi2 = tagged Invalid;

      // Test 2: Basic value member
      vi1 = tagged Valid (42);
      if (vi1.Valid !== 42) $stop;

      vi2 = tagged Valid (23 + 34);
      if (vi2.Valid !== 57) $stop;

      // Test 3: MultiType with various data types
      mt = tagged Invalid;

      mt = tagged IntVal (32'h12345678);
      if (mt.IntVal !== 32'h12345678) $stop;

      mt = tagged ShortVal (16'hABCD);
      if (mt.ShortVal !== 16'hABCD) $stop;

      mt = tagged ByteVal (8'h5A);
      if (mt.ByteVal !== 8'h5A) $stop;

      mt = tagged BitVal (1'b1);
      if (mt.BitVal !== 1'b1) $stop;

      mt = tagged Byte8 (8'hFF);
      if (mt.Byte8 !== 8'hFF) $stop;

      mt = tagged Word16 (16'h1234);
      if (mt.Word16 !== 16'h1234) $stop;

      mt = tagged Word32 (32'hDEADBEEF);
      if (mt.Word32 !== 32'hDEADBEEF) $stop;

      // Test 4: Nested tagged union (Instr example from IEEE)
      // Create an Add instruction with struct assignment pattern
      instr = tagged Add '{5'd1, 5'd2, 5'd3};
      if (instr.Add.reg1 !== 5'd1) $stop;
      if (instr.Add.reg2 !== 5'd2) $stop;
      if (instr.Add.regd !== 5'd3) $stop;

      // Create Add with named struct fields
      instr = tagged Add '{reg2:5'd10, regd:5'd20, reg1:5'd5};
      if (instr.Add.reg1 !== 5'd5) $stop;
      if (instr.Add.reg2 !== 5'd10) $stop;
      if (instr.Add.regd !== 5'd20) $stop;

      // Test 5: Nested tagged union - unconditional jump
      instr = tagged Jmp (tagged JmpU 10'd512);
      if (instr.Jmp.JmpU !== 10'd512) $stop;

      // Test 6: Nested tagged union - conditional jump
      instr = tagged Jmp (tagged JmpC '{2'd1, 10'd256});
      if (instr.Jmp.JmpC.cc !== 2'd1) $stop;
      if (instr.Jmp.JmpC.addr !== 10'd256) $stop;

      // Test 7: Nested tagged union - conditional jump with named fields
      instr = tagged Jmp (tagged JmpC '{cc:2'd3, addr:10'd100});
      if (instr.Jmp.JmpC.cc !== 2'd3) $stop;
      if (instr.Jmp.JmpC.addr !== 10'd100) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
