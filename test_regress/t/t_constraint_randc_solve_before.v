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
  constraint link_c {x >= {2'b00, c};}
endclass

class UPack;
  randc bit [1:0] c;
  rand bit [3:0] arr[3];
  constraint u_c {unique {arr};}
  constraint lim_c {c != 2'd3;}
endclass

module t;
  initial begin
    automatic Packet p = new;
    automatic UPack q = new;
    automatic bit [3:0] seen;
    automatic int npass = 0;
    automatic int upass = 0;
    for (int cycle = 0; cycle < 2; cycle++) begin
      seen = 0;
      for (int i = 0; i < 4; i++) begin
        if (p.randomize() != 0) begin
          if (p.y > p.x) npass++;
          else $stop;
          if (p.x < {2'b00, p.c}) $stop;
          if (seen[p.c]) $stop;
          seen[p.c] = 1'b1;
        end
      end
      if (seen != 4'b1111) $stop;
    end
    for (int i = 0; i < 4; i++) begin
      if (q.randomize() != 0) begin
        if (q.arr[0] == q.arr[1] || q.arr[0] == q.arr[2] || q.arr[1] == q.arr[2]) $stop;
        if (q.c == 2'd3) $stop;
        upass++;
      end
    end
    $display("NPASS=%0d UPASS=%0d", npass, upass);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
