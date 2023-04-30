// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package Pkg;
   typedef real real_t;
   real last_resolve;

   function automatic real resolver(input real drivers[]);
      resolver = 0.0;
      foreach (drivers[i]) resolver += drivers[i];
      last_resolve = resolver;
   endfunction
endpackage

module t(/*AUTOARG*/);

   function automatic real local_resolver(input real drivers[]);
      local_resolver = 0.0;
      foreach (drivers[i]) local_resolver += drivers[i];
   endfunction

   nettype real real1_n with Pkg::resolver;
   real1_n real1;
   assign real1 = 1.23;

   nettype real real2_n with local_resolver;
   real2_n real2;
   assign real2 = 1.23;

   // Create alias using new name
   nettype real2_n real3_n;
   real3_n real3;
   assign real3 = 1.23;

   nettype Pkg::real_t real4_n with Pkg::resolver;
   real4_n real4;
   assign real4 = 1.23;

   // TODO when implement net types need to check multiple driver cases, across
   // submodules

   initial begin
      #10;
      if (real1 != 1.23) $stop;
      if (real2 != 1.23) $stop;
      if (real3 != 1.23) $stop;
      if (Pkg::last_resolve != 1.23) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
