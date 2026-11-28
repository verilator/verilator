// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// One instance name at two depths (u.u, v.u) and targets written in clocked blocks next to a
// function local and an array (s, configured but not bound)
module leaf(input logic [7:0] i, output logic [7:0] o);
  logic [7:0] sig;
  assign sig = i + 8'h01;
  assign o = sig;
endmodule

module mid(input logic [7:0] i, output logic [7:0] o);
  leaf u(.i(i), .o(o));
endmodule

module other(input logic [7:0] i, output logic [7:0] o);
  leaf u(.i(i), .o(o));
endmodule

module sub (
  input logic       clk,
  input logic [7:0] a,
  output logic [7:0] q
);
  function automatic [7:0] dbl(input [7:0] op);
    reg [7:0] tmp;
    begin
      tmp = op << 1;
      dbl = tmp;
    end
  endfunction

  reg [7:0] r;

  logic [7:0] wb;
  logic [7:0] arr [0:0];

  always @(posedge clk) begin
    r  <= dbl(a);
    wb <= a;
  end

  assign arr[0] = wb;
  assign q = r ^ arr[0];
endmodule

module top_module;
  logic clk = 0;
  int cyc = 0;

  logic [7:0] ia = 8'h10;
  logic [7:0] ib = 8'h20;
  logic [7:0] oa;
  logic [7:0] ob;

  mid u(.i(ia), .o(oa));
  other v(.i(ib), .o(ob));

  logic [7:0] a = 8'd3;
  logic [7:0] q;
  sub s (.clk(clk), .a(a), .q(q));

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("[%0d] oa=%02x ob=%02x", cyc, oa, ob);
    if (cyc > 2) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
