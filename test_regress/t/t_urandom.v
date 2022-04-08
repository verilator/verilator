// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Methods defined by IEEE:
//    function int unsigned $urandom [ (int seed ) ] ;
//     function int unsigned $urandom_range( int unsigned maxval,
//                                           int unsigned minval = 0 );

module t(/*AUTOARG*/);
`ifndef VERILATOR
 `define PROC
`endif
`ifdef PROC
   process p;
`endif

   int unsigned v1;
   int unsigned v2;
   int unsigned v3;
   string       s;

   initial begin
`ifdef PROC
      if (p != null) $stop;
      p = process::self();
`endif

      v1 = $urandom;
      v2 = $urandom;
      v3 = $urandom();
      if (v1 == v2 && v1 == v3) $stop;  // Possible, but 2^-64

      // Range
      v2 = $urandom_range(v1, v1);
      if (v1 != v2) $stop;

      v2 = $urandom_range(0, 32'hffffffff);
      if (v2 == v1) $stop;

      for (int test = 0; test < 20; ++test) begin
         v1 = 2;
         v1 = $urandom_range(0, v1);
         if (v1 != 0 && v1 != 1 && v1 != 2) $stop;
         v1 = $urandom_range(2, 0);
         if (v1 != 0 && v1 != 1 && v1 !=2) $stop;
         v1 = $urandom_range(3);
         if (v1 != 0 && v1 != 1 && v1 != 2 && v1 != 3) $stop;
      end

      // Seed stability
      // Note UVM doesn't use $urandom seeding
      v1 = $urandom(1);
      v2 = $urandom(1);
      if (v1 != v2) $stop;
      v2 = $urandom(1);
      if (v1 != v2) $stop;

`ifdef PROC
      // Seed stability via process.srandom
      p.srandom(1);
      v1 = $urandom();
      p.srandom(1);
      v2 = $urandom();
      if (v1 != v2) $stop;
      p.srandom(1);
      v2 = $urandom();
      if (v1 != v2) $stop;

      // Seed stability via process.get_randstate
      s = p.get_randstate();
      v1 = $urandom();
      p.set_randstate(s);
      v2 = $urandom();
      if (v1 != v2) $stop;
      p.set_randstate(s);
      v2 = $urandom();
      if (v1 != v2) $stop;
`endif

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
