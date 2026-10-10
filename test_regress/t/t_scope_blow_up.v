// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Patrick O'Neill
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  // V3Scope and V3LinkDot used to revisit previously created scopes for each
  // instance, resulting in quadratic traversal with many instances.
  localparam int INSTANCES = 1024;
  int cyc = 0;
  wire [6:0] value = 7'(cyc);
  wire [INSTANCES-1:0][6:0] result;
  t_scope_blow_up u_leaf [INSTANCES-1:0] (.value(value), .result(result));
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc > 0) begin
      foreach (result[i]) begin
        `checkd(result[i], value ^ 7'h35);
      end
    end
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

module t_scope_blow_up (
    input logic [6:0] value,
    output logic [6:0] result
);
  // Keep the hierarchy to exercise scope traversal.
  // verilator no_inline_module
  assign result = value ^ 7'h35;
endmodule
