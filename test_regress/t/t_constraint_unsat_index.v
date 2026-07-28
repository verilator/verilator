// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Packet;
  rand bit [7:0] a;
  rand bit [7:0] b;
  constraint c {
    b > 8'd1;
    b > 8'd2;
    b > 8'd3;
    b > 8'd4;
    b > 8'd5;
    b > 8'd6;
    b > 8'd7;
    b > 8'd8;
    b > 8'd9;
    b > 8'd10;
    a > 8'd200;
    a < 8'd100;
  }
endclass

module t;
  initial begin
    automatic Packet p = new;
    if (p.randomize() != 0) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
