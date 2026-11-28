// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Hooked signals read through cross-module references
module leaf(input logic [7:0] i, output logic [7:0] o);
  logic [7:0] sig;
  logic [7:0] other;
  assign sig = i + 8'h01;
  assign other = i + 8'h02;
  assign o = sig;
endmodule

module mid(input logic [7:0] i, output logic [7:0] o);
  leaf u(.i(i), .o(o));
endmodule

module sub(output logic [7:0] inElem, output logic [7:0] inMember);
  typedef struct {
    logic [7:0] a;
    logic [7:0] b;
  } pair_t;

  logic [7:0] mem [4];
  pair_t      st;
  logic [7:0] iv = 8'h10;

  always_comb begin
    mem[0] = iv;
    mem[1] = iv + 8'h1;
    mem[2] = iv + 8'h2;
    mem[3] = iv + 8'h3;
    st.a = iv + 8'h4;
    st.b = iv + 8'h5;
  end

  assign inElem = mem[2];
  assign inMember = st.a;
endmodule

module top_module;
  logic clk = 0;
  int cyc = 0;

  logic [7:0] iv = 8'h10;
  logic [7:0] viaPort;
  mid m(.i(iv), .o(viaPort));

  logic [7:0] viaXmr;
  assign viaXmr = m.u.sig;

  logic [7:0] viaXmrOther;
  assign viaXmrOther = m.u.other;

  logic [7:0] inElem;
  logic [7:0] inMember;
  sub s(.inElem(inElem), .inMember(inMember));

  logic [7:0] outElem;
  logic [7:0] outMember;
  assign outElem = s.mem[2];
  assign outMember = s.st.a;

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("[%0d] port=%02x xmr=%02x other=%02x", cyc, viaPort, viaXmr, viaXmrOther);
    $display("[%0d] elem in=%02x out=%02x member in=%02x out=%02x", cyc, inElem, outElem,
             inMember, outMember);
    if (cyc > 2) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
