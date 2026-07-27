// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Packet;
  rand bit [7:0] a;
  rand bit [7:0] b;
  constraint c {
    a > 8'd10;
    b < 8'd200;
    a != b;
  }
endclass

module t;
  initial begin
    automatic Packet p = new;
    automatic int npass = 0;
    for (int i = 0; i < 5; i++) begin
      if (p.randomize() != 0) begin
        if (p.a > 10 && p.b < 200 && p.a != p.b) npass++;
        else $stop;
      end
    end
    $display("NPASS=%0d", npass);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
