// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Model and diversity assumption replies
class Packet;
  rand bit [7:0] a;
  rand bit [7:0] b;
  constraint c {
    a > 8'd10;
    b < 8'd200;
    a != b;
  }
endclass

// Soft constraint relaxation replies
class Softy;
  rand bit [7:0] s;
  constraint sc {
    soft s == 8'd42;
    s > 8'd100;
  }
endclass

// Phased solve...before replies
class Phased;
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint rel_c {y > x;}
endclass

module t;
  initial begin
    automatic Packet p = new;
    automatic Softy s = new;
    automatic Phased ph = new;
    automatic int npass = 0;
    automatic int rc;
    for (int i = 0; i < 4; ++i) begin
      // Below the constraint, so any model the runtime applies overwrites it
      p.a = 8'd5;
      rc = p.randomize();
      // A randomize that failed must leave the variable alone
      if (rc != 0) npass++;
      else `checkd(p.a, 8'd5);
      rc = s.randomize();
      if (rc != 0) npass++;
      rc = ph.randomize();
      if (rc != 0) npass++;
    end
    $write("NPASS=%0d\n", npass);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
