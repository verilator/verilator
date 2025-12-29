// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test if pattern matching with tagged unions
// IEEE 1800-2023 Section 12.6.2

module t;

   // Basic tagged union (IEEE example)
   typedef union tagged {
      void Invalid;
      int Valid;
   } VInt;

   // Tagged union with nested structure
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

   VInt v;
   Instr instr;
   int result;

   initial begin
      // Test 1: Basic if matches - void tag
      v = tagged Invalid;
      result = 0;
      if (v matches tagged Invalid)
         result = 1;
      else
         result = 2;
      if (result !== 1) $stop;

      // Test 2: Basic if matches - value with binding
      v = tagged Valid (42);
      result = 0;
      if (v matches tagged Valid .n)
         result = n;
      else
         result = -1;
      if (result !== 42) $stop;

      // Test 3: if-else chain
      v = tagged Valid (100);
      result = 0;
      if (v matches tagged Invalid)
         result = 1;
      else if (v matches tagged Valid .n)
         result = n;
      if (result !== 100) $stop;

      // Test 4: Nested pattern matching (IEEE example)
      instr = tagged Jmp (tagged JmpC '{2'd1, 10'd256});
      result = 0;
      if (instr matches tagged Jmp (tagged JmpC '{cc:.c, addr:.a}))
         result = a;  // 'a' is bound in pattern
      else
         result = -1;
      if (result !== 256) $stop;

      // Test 5: Chained matches with &&& (IEEE example)
      instr = tagged Jmp (tagged JmpC '{2'd2, 10'd128});
      result = 0;
      if (instr matches tagged Jmp .j &&&
          j matches tagged JmpC '{cc:.c, addr:.a})
         result = a;  // 'a' bound from second pattern
      else
         result = -1;
      if (result !== 128) $stop;

      // Test 6: Pattern with boolean filter expression
      v = tagged Valid (75);
      result = 0;
      if (v matches tagged Valid .n &&& (n > 50))
         result = 1;
      else
         result = 2;
      if (result !== 1) $stop;

      // Test 7: Pattern with boolean filter - no match
      v = tagged Valid (25);
      result = 0;
      if (v matches tagged Valid .n &&& (n > 50))
         result = 1;
      else
         result = 2;
      if (result !== 2) $stop;

      // Test 8: Scope test - bound variable only in true branch
      v = tagged Valid (99);
      result = 0;
      if (v matches tagged Valid .x) begin
         result = x;  // x is in scope here
      end
      // x is NOT in scope here (else branch / after)
      if (result !== 99) $stop;

      // Test 9: Add instruction matching
      instr = tagged Add '{5'd10, 5'd20, 5'd30};
      result = 0;
      if (instr matches tagged Add '{.r1, .r2, .rd})
         result = r1 + r2 + rd;
      else
         result = -1;
      if (result !== 60) $stop;

      // Test 10: Complex filter with register file simulation
      instr = tagged Jmp (tagged JmpC '{2'd3, 10'd100});
      result = 0;
      // If conditional jump and condition register is non-zero
      // Use nested if for boolean filter (VCS limitation with &&& after chained matches)
      if (instr matches tagged Jmp .j &&&
          j matches tagged JmpC '{cc:.c, addr:.a}) begin
         if (c != 0)
            result = a;
         else
            result = -1;
      end else
         result = -1;
      if (result !== 100) $stop;

      // Test 11: Unconditional jump matching
      instr = tagged Jmp (tagged JmpU 10'd512);
      result = 0;
      if (instr matches tagged Jmp (tagged JmpU .a))
         result = a;
      else
         result = -1;
      if (result !== 512) $stop;

      // Test 12: Wildcard pattern in if
      instr = tagged Add '{5'd1, 5'd2, 5'd3};
      result = 0;
      if (instr matches tagged Add .*)
         result = 1;
      else if (instr matches tagged Jmp .*)
         result = 2;
      if (result !== 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
