// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// The binding is sampled at time zero, so paths written later hook nothing and final() warns
module leaf(input logic [7:0] i, output logic [7:0] o);
  logic [7:0] sig;
  assign sig = i + 8'h01;
  assign o = sig;
endmodule

module wrapA(input logic [7:0] i, output logic [7:0] o);
  leaf u(.i(i), .o(o));
endmodule

module wrapB(input logic [7:0] i, output logic [7:0] o);
  leaf u(.i(i), .o(o));
endmodule

module top_module;
  logic clk = 0;
  int cyc = 0;

  logic [7:0] ia = 8'h10;
  logic [7:0] ib = 8'h20;
  logic [7:0] oa;
  logic [7:0] ob;

  wrapA a(.i(ia), .o(oa));
  wrapB b(.i(ib), .o(ob));

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("[%0d] oa=%02x ob=%02x", cyc, oa, ob);
    if (cyc > 5) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
