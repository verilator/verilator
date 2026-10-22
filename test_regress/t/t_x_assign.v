// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2020 Geza Lore
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Converting the X in the package's first statement must not stop the X in
// the statements after it from being converted too
package pkg;
  function automatic logic [31:0] first();
    return 'x;
  endfunction
  function automatic logic [31:0] second();
    return 'x;
  endfunction
endpackage

module t_x_assign (
    input wire clk,
    output reg o,
    output reg [31:0] o_int,
    output reg [31:0] o_first,
    output reg [31:0] o_second
);
  always @(posedge clk) begin
    if (1'bx) o <= 1'd1;
    else o <= 1'd0;
    o_int <= 'x;
    o_first <= pkg::first();
    o_second <= pkg::second();
  end
endmodule
