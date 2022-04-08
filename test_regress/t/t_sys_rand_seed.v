// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   integer seeda;
   integer seedb;
   integer seedc;
   int valuea;
   int valueb;
   int valuec;

   initial begin
      // $random unlike $urandom updates the value if given
      seeda = 10;
      valuea = $random(seeda);
      seedb = 10;
      valueb = $random(seedb);
      if (valuea !== valueb) $stop;

      seeda = 10;
      valuea = $random(seeda);
      seedb = seeda;
      valueb = $random(seedb);
      seedc = seedb;
      valuec = $random(seedc);
      if (valuea == valueb && valueb == valuec) $stop;  // May false fail 1 in 1^64
      if (seeda == seedb && seedb == seedc) $stop;  // May false fail 1 in 1^64

      valuea = $urandom(10);
      valueb = $urandom(10);
      if (valuea !== valueb) $stop;

      valuea = $urandom(10);
      valueb = $urandom();
      valuec = $urandom();
      if (valuea == valueb && valueb == valuec) $stop;  // May false fail 1 in 1^64

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
