// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Packet;
  randc bit [1:0] c;
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint rel_c {y > x;}
endclass

module t;
  initial begin
    automatic Packet p = new;
    automatic bit [3:0] seen;
    automatic int npass = 0;
    for (int cycle = 0; cycle < 2; cycle++) begin
      seen = 0;
      for (int i = 0; i < 4; i++) begin
        if (p.randomize() != 0) begin
          if (p.y > p.x) npass++;
          else $stop;
          if (seen[p.c]) $stop;
          seen[p.c] = 1'b1;
        end
      end
      if (seen != 4'b1111) $stop;
    end
    $display("NPASS=%0d", npass);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
