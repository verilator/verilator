// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
   longint     a;
   longint     b;
   longint     c;
} s_t;

module t;
   localparam int         c0 [4] = '{5,  6,  7,  8};
   localparam bit [255:0] c1 [4] = '{9, 10, 11, 12};
   localparam string      c2 [2] = '{"baz", "quux"};
   localparam s_t         c3 [2] = '{'{a:  100, b:  200, c:  300},
                                     '{a: 1000, b: 2000, c: 3000}};

   a #(
       .p0(c0),
       .p1(c1),
       .p2(c2),
       .p3(c3)
       ) i_a ();
endmodule

module a
  #(
    parameter int         p0 [4] = '{1, 2, 3, 4},
    parameter bit [255:0] p1 [4] = '{1, 2, 3, 4},
    parameter string      p2 [2] = '{"foo", "bar"},
    parameter s_t         p3 [2] = '{'{a: 1, b: 2, c: 3},
                                     '{a: 1, b: 2, c: 3}}
    );

   int i;

   initial begin
      // Go via $c to ensure parameters are emitted
      i = $c("0"); if (p0[i] !=  5) $stop;
      i = $c("1"); if (p0[i] !=  6) $stop;
      i = $c("2"); if (p0[i] !=  7) $stop;
      i = $c("3"); if (p0[i] !=  8) $stop;
      i = $c("0"); if (p1[i] !=  9) $stop;
      i = $c("1"); if (p1[i] != 10) $stop;
      i = $c("2"); if (p1[i] != 11) $stop;
      i = $c("3"); if (p1[i] != 12) $stop;
      i = $c("0"); if (p2[i] != "baz") $stop;
      i = $c("1"); if (p2[i] != "quux") $stop;
      i = $c("0"); if (p3[i].a != 100) $stop;
      i = $c("0"); if (p3[i].b != 200) $stop;
      i = $c("0"); if (p3[i].c != 300) $stop;
      i = $c("1"); if (p3[i].a != 1000) $stop;
      i = $c("1"); if (p3[i].b != 2000) $stop;
      i = $c("1"); if (p3[i].c != 3000) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
