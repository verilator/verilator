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
   initial begin
      // Go via $c to ensure parameters are emitted
      if (p0[$c("0")] !=  5) $stop;
      if (p0[$c("1")] !=  6) $stop;
      if (p0[$c("2")] !=  7) $stop;
      if (p0[$c("3")] !=  8) $stop;
      if (p1[$c("0")] !=  9) $stop;
      if (p1[$c("1")] != 10) $stop;
      if (p1[$c("2")] != 11) $stop;
      if (p1[$c("3")] != 12) $stop;
      if (p2[$c("0")] != "baz") $stop;
      if (p2[$c("1")] != "quux") $stop;
      if (p3[$c("0")].a != 100) $stop;
      if (p3[$c("0")].b != 200) $stop;
      if (p3[$c("0")].c != 300) $stop;
      if (p3[$c("1")].a != 1000) $stop;
      if (p3[$c("1")].b != 2000) $stop;
      if (p3[$c("1")].c != 3000) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
