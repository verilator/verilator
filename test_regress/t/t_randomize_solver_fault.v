// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Packet;
`ifdef T_STALL
  rand bit [7:0] arr[4096];
  constraint c {foreach (arr[i]) arr[i] > 8'd1;}
`elsif T_UNSAT
  rand bit [7:0] a;
  constraint c {
    a > 8'd200;
    a < 8'd100;
  }
`elsif T_PINNED
  rand bit [15:0] a;
  constraint c {a == 16'h5a5a;}
`elsif T_SOFT
  rand bit [7:0] a;
  constraint c {
    soft a == 8'd42;
    soft a == 8'd57;
  }
`elsif T_PHASED
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint rel_c {y > x;}
`else
  rand bit [7:0] a;
  rand bit [7:0] b;
  constraint c {
    a > 8'd10;
    b < 8'd200;
    a != b;
  }
`endif
endclass

module t;
  initial begin
    automatic Packet p = new;
`ifdef T_MODEL
    automatic int rc;
    p.a = 8'd77;
    rc = p.randomize();
    if (rc != 0) $stop;
    if (p.a != 8'd77) $stop;
    rc = p.randomize();
    if (rc == 0) $stop;
    if (!(p.a > 8'd10)) $stop;
`elsif T_STALL
    automatic int nfail = 0;
    for (int i = 0; i < 3; i++) begin
      if (p.randomize() == 0) nfail++;
    end
    $display("NFAIL=%0d", nfail);
`elsif T_UNSAT
    automatic int nfail = 0;
    for (int i = 0; i < 5; i++) begin
      if (p.randomize() == 0) nfail++;
    end
    $display("NFAIL=%0d", nfail);
`elsif T_PINNED
    automatic int npass = 0;
    for (int i = 0; i < 5; i++) begin
      if (p.randomize() != 0) begin
        if (p.a == 16'h5a5a) npass++;
        else $stop;
      end
    end
    $display("NPASS=%0d", npass);
`elsif T_SOFT
    automatic int npass = 0;
    automatic int nsoft = 0;
    for (int i = 0; i < 5; i++) begin
      if (p.randomize() != 0) begin
        npass++;
        if (p.a == 8'd42 || p.a == 8'd57) nsoft++;
      end
    end
    $display("NPASS=%0d NSOFT=%0d", npass, nsoft);
`elsif T_PHASED
    automatic int npass = 0;
    for (int i = 0; i < 5; i++) begin
      if (p.randomize() != 0) begin
        if (p.y > p.x) npass++;
        else $stop;
      end
    end
    $display("NPASS=%0d", npass);
`else
    automatic int npass = 0;
    for (int i = 0; i < 5; i++) begin
      if (p.randomize() != 0) begin
        if (p.a > 10 && p.b < 200 && p.a != p.b) npass++;
        else $stop;
      end
    end
    $display("NPASS=%0d", npass);
`endif
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
