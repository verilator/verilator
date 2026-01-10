// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: CC0-1.0

// Test to check whether the following spec is properly implemented.
// In IEEE 1800-2023 7.4.1 Packed arrays:
//   If a packed array is declared as signed, then the array viewed as a single
//   vector shall be signed. The individual elements of the array are unsigned
//   unless they are of a named type declared as signed.

module t;
   typedef logic signed [2:0] named_t;
   typedef named_t [1:0] named_named_t;
   typedef logic signed [1:0][2:0] named_unnamed_t;

   named_named_t [1:0] named_named;
   named_unnamed_t [1:0] named_unnamed;
   logic signed [1:0][1:0][2:0] unnamed;

   initial begin
      // Set 1 to MSB(=sign bit)
      named_named = 12'b100000_000000;
      named_unnamed = 12'b100000_000000;
      unnamed = 12'b100000_000000;

      if ($signed((named_named >>> 1) >> 11) != 0) begin
         $stop;
      end
      if ($signed((named_named[1] >>> 1) >> 5) != 0) begin
         $stop;
      end
      if ($signed((named_named[1][1] >>> 1) >> 2) != 1) begin
         $stop;
      end

      if ($signed((named_unnamed >>> 1) >> 11) != 0) begin
         $stop;
      end
      if ($signed((named_unnamed[1] >>> 1) >> 5) != 1) begin
         $stop;
      end
      if ($signed((named_unnamed[1][1] >>> 1) >> 2) != 0) begin
         $stop;
      end

      if ($signed((unnamed >>> 1) >> 11) != 1) begin
          $stop;//
      end
      if ($signed((unnamed[1] >>> 1) >> 5) != 0) begin
         $stop;
      end
      if ($signed((unnamed[1][1] >>> 1) >> 2) != 0) begin
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
