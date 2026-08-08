// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class PktLo;
  rand bit [7:0] a;
  constraint c {
    a >= 8'd20;
    a <= 8'd30;
  }
endclass

class PktHi;
  rand bit [7:0] b;
  constraint c {
    b >= 8'd100;
    b <= 8'd110;
  }
endclass

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
    if (p.randomize() != 0) begin
      if (p.a >= 20 && p.a <= 30) npass <= npass + 1;
      else $stop;
    end
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
  always @(posedge clk) begin
    phase <= phase + 1;
    if (phase[0] == 1'b0) begin
      if (p.randomize() != 0) begin
        if (p.b >= 100 && p.b <= 110) npass <= npass + 1;
        else $stop;
      end
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
      if (nlo != 99 || nhi != 50) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
