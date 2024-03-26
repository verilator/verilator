// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

int N = 10;

class Cls;
   rand bit [127:0] dyn[];

   function new;
      dyn = new[N];
   endfunction

   function Cls copy;
      Cls cl = new;

      foreach (dyn[i])
         cl.dyn[i] = dyn[i];
      return cl;
   endfunction

   function bit is_equal(Cls cl);
      foreach (dyn[i])
         if (dyn[i] != cl.dyn[i])
            return 0;
      return 1;
   endfunction
endclass

module t;
   initial begin
      Cls a = new;
      Cls b = new;

      // Check scope randomization
      for (int i = 0; i < N; i++) begin
         void'(std::randomize());
         if (a.is_equal(b))
            $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
