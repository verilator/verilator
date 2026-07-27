// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Packet;
  rand bit [7:0] a;
  constraint c {
    a > 8'd200;
    a < 8'd100;
  }
endclass

module t;
  initial begin
    automatic Packet p = new;
    automatic int nfail = 0;
    for (int i = 0; i < 5; i++) begin
      if (p.randomize() == 0) nfail++;
    end
    $display("NFAIL=%0d", nfail);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
