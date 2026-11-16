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
// unsat core report. The variable has the form of the runtime's numbered core
// labels (__Vcons<N>) without the prefix, and must not clash.
class Unsat;
  rand bit [7:0] cons0;
  constraint uc {
    cons0 > 8'd200;
    cons0 < 8'd100;
  }
endclass

module t;
  initial begin
    automatic Unsat un = new;
    automatic int nfail = 0;
    for (int i = 0; i < 3; ++i) begin
      un.cons0 = 8'd7;
      if (un.randomize() == 0) nfail++;
      // An unsatisfiable randomize leaves the variable alone
      `checkd(un.cons0, 8'd7);
    end
    $write("NFAIL=%0d\n", nfail);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
