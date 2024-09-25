// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

typedef enum {efgh} en;

module t (/*AUTOARG*/);
   initial begin
      en e;
      string s;

      s = {"a", "b"};
      if (s != "ab") $stop;

      e = efgh;
      s = {"abcd", e.name(), "ijkl"};
      if (s != "abcdefghijkl") $stop;

      // hang V3Width if complexity grows exponential (2**52 should suffice)
      s = {"a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
           "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z",
           "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
           "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"};
      if (s != "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz") $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
