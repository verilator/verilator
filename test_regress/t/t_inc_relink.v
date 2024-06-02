// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

// Test if temporary vars are relinked if not used directly under FTASK.

package A;  // Create JUMPBLOCK; use n++ in it
   task t;
      automatic int n;
      if ($random) return;
      n = n++;
   endtask
endpackage

package B;  // Create IF; use n++ in it
   int n;
   task t;
      if ($random) n = n++;
   endtask
endpackage

module C;  // Like above but in a module
   int n = 0;

   initial if ($random) n = n++;
endmodule

module t;  // Actually use those to test relinking
   C c;

   initial begin
      A::t();
      B::t();
   end
endmodule
