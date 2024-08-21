// DESCRIPTION: Verilator: Dotted reference that uses another dotted reference
// as the select expression
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   o,
   // Inputs
   i
   );
   input i;
   output o;
   sub sub (.i, .o);
endmodule

module sub(/*AUTOARG*/
   // Outputs
   o,
   // Inputs
   i
   );
   input i;
   output o;
   assign o = !i;
endmodule
