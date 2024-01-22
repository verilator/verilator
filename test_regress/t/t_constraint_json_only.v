// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int header;  // 0..7
   rand int length;  // 0..15
   rand int sublength; // 0..15
   rand bit if_4;
   rand bit iff_5_6;

   rand int array[2];  // 2,4,6

   constraint empty {}

   constraint size {
      header > 0 && header <= 7;
      length <= 15;
      length >= header;
      length dist { [0:1], [2:5] :/ 2, 6 := 6, 7 := 10, 1};
   }

   constraint ifs {
      if (header > 4) {
         if_4 == '1;
      }
      if (header == 5 || header == 6) {
         iff_5_6 == '1;
      } else {
         iff_5_6 == '0;
      }
   }

   constraint arr_uniq {
      foreach (array[i]) {
         array[i] inside {2, 4, 6};
      }
      unique { array[0], array[1] }
   }

   constraint order { solve length before header; }

   constraint dis {
      soft sublength;
      disable soft sublength;
      sublength <= length;
   }

endclass

module t (/*AUTOARG*/);

   Packet p;

   initial begin
      // Not testing use of constraints
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
