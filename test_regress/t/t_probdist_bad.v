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

   initial begin
      // Illegal values
      r = $dist_chi_square(seed, 0);
      if (r != 0 && !$isunknown(r)) $stop;
      r = $dist_erlang(seed, 0, 0);
      if (r != 0 && !$isunknown(r)) $stop;
      r = $dist_exponential(seed, 0);
      if (r != 0 && !$isunknown(r)) $stop;
      // r =$dist_exponential(seed, mean);  // Always valid
      r = $dist_poisson(seed, 0);
      if (r != 0 && !$isunknown(r)) $stop;
      r = $dist_t(seed, 0);
      if (r != 0 && !$isunknown(r)) $stop;
      r = $dist_uniform(seed, 10, 0);
      if (r != 10 && !$isunknown(r)) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
