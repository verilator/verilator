// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test unique constraint support.
// unique { a, b, c } expands to: a != b, a != c, b != c

class unique_pair;
   rand bit [15:0] p;
   rand bit [15:0] q;

   constraint c_unique { unique { p, q }; }

   function new();
      p = 0;
      q = 0;
   endfunction

   function void check();
      if (p == q) begin
         $display("ERROR: p == q (%0d)", p);
         $stop;
      end
   endfunction
endclass

// Test with 3 variables: generates 3 pairwise constraints (a!=b, a!=c, b!=c)
class unique_triple;
   rand bit [7:0] a;
   rand bit [7:0] b;
   rand bit [7:0] c;

   constraint c_unique { unique { a, b, c }; }

   function new();
      a = 0;
      b = 0;
      c = 0;
   endfunction

   function void check();
      if (a == b) begin
         $display("ERROR: a == b (%0d)", a);
         $stop;
      end
      if (a == c) begin
         $display("ERROR: a == c (%0d)", a);
         $stop;
      end
      if (b == c) begin
         $display("ERROR: b == c (%0d)", b);
         $stop;
      end
   endfunction
endclass

module t;
   unique_pair obj_pair;
   unique_triple obj_triple;

   initial begin
      // Test pair
      obj_pair = new();
      repeat(10) begin
         if (obj_pair.randomize() != 1) begin
            $display("ERROR: randomize() failed for pair");
            $stop;
         end
         obj_pair.check();
         $display("Pair: p=%0d, q=%0d", obj_pair.p, obj_pair.q);
      end

      // Test triple
      obj_triple = new();
      repeat(10) begin
         if (obj_triple.randomize() != 1) begin
            $display("ERROR: randomize() failed for triple");
            $stop;
         end
         obj_triple.check();
         $display("Triple: a=%0d, b=%0d, c=%0d", obj_triple.a, obj_triple.b, obj_triple.c);
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
