// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t(/*AUTOARG*/);

   integer seed;
   integer r;
   integer sum;

   initial begin
      //=======
      seed = 1234;
      r = $dist_chi_square(seed, 5);
      `checkd(seed, 923940542);
      `checkd(r, 8);
      sum = 1;
      repeat(20) sum += $dist_chi_square(seed, 5);
      `checkd(sum, 130);
      sum = 1;
      repeat(20) sum += $dist_chi_square(seed, -5);
      `checkd(sum, 1);
      sum = 1;
      repeat(20) sum += $dist_chi_square(seed, 2);
      `checkd(sum, 30);

      //=======
      seed = 1234;
      r = $dist_erlang(seed, 5, 10);
      `checkd(seed, 1025211431);
      `checkd(r, 19);
      sum = 1;
      repeat(20) sum += $dist_erlang(seed, 5, 10);
      `checkd(sum, 173);
      sum = 1;
      repeat(20) sum += $dist_erlang(seed, 5, -10);
      `checkd(sum, -241);

      //=======
      seed = 1234;
      r = $dist_exponential(seed, 5);
      `checkd(seed, 85231147);
      `checkd(r, 20);
      sum = 1;
      repeat(20) sum += $dist_exponential(seed, 5);
      `checkd(sum, 104);

      //=======
      seed = 1234;
      r = $dist_normal(seed, 5, 10);
      `checkd(seed, -1570070672);
      `checkd(r, 4);
      sum = 1;
      repeat(20) sum += $dist_normal(seed, 5, 10);
      `checkd(sum, 114);

      //=======
      seed = 1234;
      r = $dist_poisson(seed, 5);
      `checkd(seed, 418012337);
      `checkd(r, 2);
      sum = 1;
      repeat(20) sum += $dist_poisson(seed, 5);
      `checkd(sum, 111);

      //=======
      seed = 1234;
      r = $dist_t(seed, 5);
      `checkd(seed, -797481412);
      `checkd(r, 0);
      sum = 1;
      repeat(20) sum += $dist_t(seed, 5);
      `checkd(sum, -2);

      //=======
      seed = 1234;
      r = $dist_uniform(seed, 5, 10);
      `checkd(seed, 85231147);
      `checkd(r, 5);
      sum = 1;
      repeat(20) sum += $dist_uniform(seed, 5, 10);
      `checkd(sum, 147);

      seed = 1234;
      r = $dist_uniform(seed, 10, 5);
      `checkd(r, 10);
      sum = 1;
      repeat(20) sum += $dist_uniform(seed, -2147483648, -20);
      `checkd(sum, 1768955681);
      sum = 1;
      repeat(20) sum += $dist_uniform(seed, 20, 2147483647);
      `checkd(sum, 1534326415);
      sum = 1;
      repeat(20) sum += $dist_uniform(seed, -2147483648, 2147483647);
      `checkd(sum, 1394525852);
      seed = 0;
      sum = 1;
      repeat(20) sum += $dist_uniform(seed, -10, 100);
      `checkd(seed, 1003647461);
      `checkd(sum, 896);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
