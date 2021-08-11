// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2021 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// From issue #3096

module decoder(
               input wire [31:0] instr_i,
               // Making 'a' an output preserves it as a sub-expression and causes a missing clean
               output wire       a,
               output wire       illegal_instr_o
               );
   /* verilator lint_off WIDTH */
   wire                          b = ! instr_i[12:5];
   wire                          c = ! instr_i[1:0];
   wire                          d = ! instr_i[15:13];
   /* verilator lint_on WIDTH */
   assign a = d ? b : 1'h1;
   assign illegal_instr_o = c ? a : 1'h0;
endmodule
