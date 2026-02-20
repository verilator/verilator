// DESCRIPTION: Verilator: Dotted reference that uses another dotted reference
// as the select expression
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
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
