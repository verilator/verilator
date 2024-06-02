// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   process p;

   integer seed;
   string state;
   int a;
   int b;

   initial begin
      p = process::self();

      // Test setting RNG state with state string
      state = p.get_randstate();
      p.set_randstate(state);
      a = $random;
      p.set_randstate(state);
      b = $random;
      $display("a=%d, b=%d", a, b);
      if (a != b) $stop;

      // Test the same with $urandom
      state = p.get_randstate();
      p.set_randstate(state);
      a = $urandom;
      p.set_randstate(state);
      b = $urandom;
      $display("a=%d, b=%d", a, b);
      if (a != b) $stop;

      // Test if the results repeat after the state is reset
      state = p.get_randstate();
      for (int i = 0; i < 10; i++)
         $random;
      a = $random;
      // Now reset the state and take 11th result again
      p.set_randstate(state);
      for (int i = 0; i < 10; i++)
         $random;
      b = $random;
      $display("a=%d, b=%d", a, b);
      if (a != b) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
