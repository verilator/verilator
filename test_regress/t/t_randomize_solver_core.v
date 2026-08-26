// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Only unsatisfiable, so every solver status this test produces belongs to the
// unsat core report
class Unsat;
  rand bit [7:0] u;
  constraint uc {
    u > 8'd200;
    u < 8'd100;
  }
endclass

module t;
  initial begin
    automatic Unsat un = new;
    automatic int nfail = 0;
    for (int i = 0; i < 3; ++i) begin
      un.u = 8'd7;
      if (un.randomize() == 0) nfail++;
      // An unsatisfiable randomize leaves the variable alone
      `checkd(un.u, 8'd7);
    end
    $write("NFAIL=%0d\n", nfail);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
