// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Each class pins one value, so a reply delivered to the wrong transaction
// shows up as a wrong value rather than as a rare miscount
class PktLo;
  rand bit [7:0] a;
  constraint c {a == 8'd25;}
endclass

class PktHi;
  rand bit [7:0] b;
  constraint c {b == 8'd105;}
endclass

// Two modules randomize on the same edge, so the runtime has to serialize the
// solver transactions of the threads running them
module sub_lo (
    input logic clk,
    output int npass
);
  PktLo p;
  initial begin
    p = new;
    npass = 0;
  end
  always @(posedge clk) begin
    automatic int rc = p.randomize();
    `checkd(rc, 1);
    `checkd(p.a, 8'd25);
    npass <= npass + 1;
  end
endmodule

module sub_hi (
    input logic clk,
    output int npass
);
  PktHi p;
  int phase;
  initial begin
    p = new;
    npass = 0;
    phase = 0;
  end
  // Randomizes every other edge, so the two modules also collide unevenly
  always @(posedge clk) begin
    phase <= phase + 1;
    if (phase[0] == 1'b0) begin
      automatic int rc = p.randomize();
      `checkd(rc, 1);
      `checkd(p.b, 8'd105);
      npass <= npass + 1;
    end
  end
endmodule

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;
  int nlo, nhi;
  int cyc = 0;
  sub_lo u_lo (
      .clk(clk),
      .npass(nlo)
  );
  sub_hi u_hi (
      .clk(clk),
      .npass(nhi)
  );
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 99) begin
      $display("NLO=%0d NHI=%0d", nlo, nhi);
      `checkd(nlo, 99);
      `checkd(nhi, 50);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
