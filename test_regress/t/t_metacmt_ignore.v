// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   reg [0:1] show1;                                     // Should warn
   /*verilator lint_ignore LITENDIAN*/ reg [0:2] ign2;  // Should not warn
   reg [0:3] show3;                                     // Should warn
   reg [0:4] ign4; /*verilator lint_ignore LITENDIAN*/  // Should not warn
   reg [0:5] show5;                                     // Should warn
   reg [0:6] ign6; /*verilator lint_ignore LITENDIAN*/ reg [0:7] ign7; // Should not warn
   reg [0:8] ign8; // verilator lint_ignore LITENDIAN      Should not warn
   reg [0:9] show9;                                     // Should not warn
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
