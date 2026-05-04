// DESCRIPTION: Verilator: AstConst originating parameter name
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t(input logic [1:0] state,
         output logic direct_named,
         output logic computed_named,
         output logic anonymous_expr);

   localparam logic [1:0] S_IDLE = 2'b00;
   localparam logic [1:0] S_FETCH = 2'b01;
   localparam logic [1:0] S_EXEC = S_FETCH + 1;

   assign direct_named = state == S_IDLE;
   assign computed_named = state == S_EXEC;
   assign anonymous_expr = state == (S_FETCH + 1);

endmodule
