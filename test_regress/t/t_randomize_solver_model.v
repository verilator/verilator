// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Packet;
  rand bit [7:0] a;
  constraint c {a > 8'd10;}
endclass

module t;
  initial begin
    automatic Packet p = new;
    automatic int rc;
    p.a = 8'd77;
    rc = p.randomize();
    if (rc != 0) $stop;
    if (p.a != 8'd77) $stop;
    rc = p.randomize();
    if (rc == 0) $stop;
    if (!(p.a > 8'd10)) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
