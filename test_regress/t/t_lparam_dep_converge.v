// DESCRIPTION: Verilator: Converge dependent localparams after parameterized class linking
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Petr Nohavica
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// The declarations are intentionally in reverse dependency order.  The member-projection graph
// publishes C5::M, then the deferred-parameter graph publishes B and D from that semantic fact.
class C #(parameter int V = 3);
  localparam int M = V * 2;
endclass

module t;
  typedef C#(5) C5;
  localparam int D = B * 2;
  localparam int B = A + 1;
  localparam int A = C5::M;

  // This fact is collected before V3Param folds the generate.  Its source and consumer are
  // deliberately discarded without specialization, exercising quiescent fact retirement and
  // the deferred AST-ownership boundary.
  if (0) begin : dead_projection
    typedef C#(7) DeadC;
    localparam int DEAD = DeadC::M;
  end

  initial begin
    `checkd(D, 22);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
