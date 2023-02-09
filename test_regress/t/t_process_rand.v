// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   process p;

   integer seed;
   string state;
   int valuea;
   int valueb;

   initial begin
      p = process::self();

      seed = 43;

      // Test setting seed
      p.srandom(seed);
      valuea = $random;
      p.srandom(seed);
      valueb = $random;
      if (valuea != valueb) $stop;

      // Test setting is with state string
      state = p.get_randstate();
      p.set_randstate(state);
      valuea = $random;
      p.set_randstate(state);
      valueb = $random;
      if (valuea != valueb) $stop;

      // Test the same with $urandom
      p.srandom(seed);
      valuea = $urandom;
      p.srandom(seed);
      valueb = $urandom;
      if (valuea != valueb) $stop;

      state = p.get_randstate();
      p.set_randstate(state);
      valuea = $urandom;
      p.set_randstate(state);
      valueb = $urandom;
      if (valuea != valueb) $stop;

      // Test if the results repeat after the state is reset
      state = p.get_randstate();
      for (int i = 0; i < 10; i++)
         $random;
      valuea = $random;
      // Now reset the state and take 11th result again
      p.set_randstate(state);
      for (int i = 0; i < 10; i++)
         $random;
      valueb = $random;
      if (valuea != valueb) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
